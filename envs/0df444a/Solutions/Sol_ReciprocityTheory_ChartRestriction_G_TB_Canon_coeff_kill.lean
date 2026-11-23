-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.coeff_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:55.430795+00:00
-- url     : https://prove2.me/submissions/22303884-0db3-40cc-92bb-f76952823ec1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (j : Fin n) (f : PS k n d) (m : Fin n × Fin d →₀ ℕ) :
    coeff m (sb (Function.update gen j 0) f) = if ∀ b, m (j, b) = 0 then coeff m f else 0 := by
  let a : Fin n × Fin d → PS k n d := fun p => ((Function.update gen j 0 p.1 : Q k d n) : Pt k n d) p.2
  have ha : MvPowerSeries.HasSubst a := (czQ (Function.update gen j 0)).hasSubst
  have key : ∀ e : Fin n × Fin d →₀ ℕ, coeff m (e.prod fun s i => a s ^ i) =
      if e = m ∧ ∀ b, m (j, b) = 0 then 1 else 0 := by
    intro e
    by_cases he : ∀ b, e (j, b) = 0
    · have hp : (e.prod fun s i => a s ^ i) = MvPowerSeries.monomial e 1 := by
        refine (Finsupp.prod_congr fun s hs => ?_).trans (MvPowerSeries.monomial_one_eq e).symm
        have hs1 : s.1 ≠ j := by
          intro h1
          apply Finsupp.mem_support_iff.mp hs
          rw [show s = (j, s.2) from Prod.ext h1 rfl]
          exact he s.2
        show ((Function.update gen j 0 s.1 : Q k d n) : Pt k n d) s.2 ^ e s = X s ^ e s
        rw [Function.update_of_ne hs1]
        rfl
      rw [hp, MvPowerSeries.coeff_monomial]
      by_cases hem : e = m
      · subst hem
        simp [he]
      · rw [if_neg (Ne.symm hem), if_neg (fun h => hem h.1)]
    · push_neg at he
      obtain ⟨b, hb⟩ := he
      have hp : (e.prod fun s i => a s ^ i) = 0 := by
        refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hb) ?_
        show ((Function.update gen j 0 j : Q k d n) : Pt k n d) b ^ e (j, b) = 0
        first
        | rw [Function.update_self]
        | rw [Function.update_same]
        exact zero_pow hb
      rw [hp, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hb (h b)
  rw [sb_apply]
  show coeff m (MvPowerSeries.subst a f) = _
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · show coeff m f • coeff m (m.prod fun s i => a s ^ i) = _
    rw [key]
    by_cases hm : ∀ b, m (j, b) = 0 <;> simp [hm]
  · intro e he
    show coeff e f • coeff m (e.prod fun s i => a s ^ i) = 0
    rw [key, if_neg (fun h => he h.1), smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
