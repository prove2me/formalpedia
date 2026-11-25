-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_le_height_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:00.285174+00:00
-- url     : https://prove2.me/submissions/5f801b16-733b-40c5-a35a-ad2494aeed80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_isPrime_map_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_comap_map_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
variable {A : Type*} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {I q M : Ideal A} [q.IsPrime] [M.IsPrime] (hIq : I ≤ q)
    (hqM : q ≤ M) (H : ∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ M → q ≤ P) :
    (M.map (Ideal.Quotient.mk I)).height ≤ (M.map (Ideal.Quotient.mk q)).height := by
  have hMI : (M.map (Ideal.Quotient.mk I)).IsPrime := isPrime_map_mk (hIq.trans hqM)
  have hMq : (M.map (Ideal.Quotient.mk q)).IsPrime := isPrime_map_mk hqM
  rw [(⟨_, hMI⟩ : PrimeSpectrum (A ⧸ I)).height_eq_orderHeight,
    (⟨_, hMq⟩ : PrimeSpectrum (A ⧸ q)).height_eq_orderHeight]
  refine Order.height_le fun p hp => ?_
  have hbelow : ∀ i, (p i).asIdeal.comap (Ideal.Quotient.mk I) ≤ M := fun i => by
    have : p i ≤ p.last := p.monotone (Fin.le_last _)
    rw [hp, ← PrimeSpectrum.asIdeal_le_asIdeal] at this
    calc _ ≤ (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := Ideal.comap_mono this
      _ = M := comap_map_mk (hIq.trans hqM)
  have hmem : ∀ i, q ≤ (p i).asIdeal.comap (Ideal.Quotient.mk I) := fun i => by
    refine H _ (Ideal.comap_isPrime _ _) ?_ (hbelow i)
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  let f : Fin (p.length + 1) → PrimeSpectrum (A ⧸ q) := fun i =>
    ⟨((p i).asIdeal.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk q), isPrime_map_mk (hmem i)⟩
  have step : ∀ i : Fin p.length, f i.castSucc < f i.succ := by
    intro i
    have h2 : (p i.castSucc).asIdeal.comap (Ideal.Quotient.mk I) <
        (p i.succ).asIdeal.comap (Ideal.Quotient.mk I) := by
      have := RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective (p.step i)
      exact this
    refine lt_of_le_of_ne (Ideal.map_mono h2.le) fun e => h2.ne ?_
    have := congrArg (fun J => J.comap (Ideal.Quotient.mk q)) (congrArg PrimeSpectrum.asIdeal e)
    simpa [f, comap_map_mk (hmem _)] using this
  let p' : LTSeries (PrimeSpectrum (A ⧸ q)) := ⟨p.length, f, step⟩
  have : p'.last ≤ ⟨_, hMq⟩ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.map_mono (hbelow _)
  exact Order.length_le_height this
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
