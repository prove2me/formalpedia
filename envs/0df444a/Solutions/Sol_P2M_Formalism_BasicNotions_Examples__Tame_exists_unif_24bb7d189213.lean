-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_exists_unif_24bb7d189213
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:51.721343+00:00
-- url     : https://prove2.me/submissions/e1327d25-454a-4635-8e76-23cc55b19770

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (L : Type) [Field L] [NumberField L] (i : L →+* Ω) (p : ℕ) (hp0 : p ≠ 0)
    (hp : A.valuation (p : Ω) < 1) :
    ∃ π : L, π ≠ 0 ∧ ∀ y : L, y ≠ 0 → ∃ n : ℤ, A.valuation (i (y / π ^ n)) = 1 := by
  have hint : ∀ x : 𝓞 L, i (x : L) ∈ A := fun x => by
    have h1 : IsIntegral ℤ (i (x : L)) := (RingOfIntegers.isIntegral_coe x).map i.toIntAlgHom
    have h2 : IsIntegral A (i (x : L)) := h1.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h2
    rw [← hy]; exact y.2
  let j : 𝓞 L →+* A := (i.comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap j
  have hP : ∀ x : 𝓞 L, x ∈ P ↔ A.valuation (i (x : L)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (j x)
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, fun hb => by
    have : (p : 𝓞 L) ∈ P := (hP _).mpr (by simpa using hp)
    rw [hb, Ideal.mem_bot] at this
    exact hp0 (by exact_mod_cast this)⟩
  have hunit : ∀ x : 𝓞 L, x ∉ P → A.valuation (i (x : L)) = 1 := fun x hx =>
    le_antisymm ((A.valuation_le_one_iff _).mpr (hint x)) (not_lt.mp fun h => hx ((hP x).mpr h))
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, hπ0, fun y hy => ⟨-WithZero.log (w.valuation L y), ?_⟩⟩
  have hv : w.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have h1 : w.valuation L (y / π ^ (-WithZero.log (w.valuation L y))) = 1 := by
    rw [map_div₀, map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  generalize y / π ^ (-WithZero.log (w.valuation L y)) = z at h1
  obtain ⟨a, b, hab⟩ := w.exists_primeCompl_mul_eq_of_integer z h1.le
  have hb : A.valuation (i ((b : 𝓞 L) : L)) = 1 := hunit _ b.2
  have ha : a ∉ P := by
    intro ha
    have h2 : w.valuation L (algebraMap (𝓞 L) L a) < 1 := (w.valuation_lt_one_iff_mem _).mpr ha
    have h3 : w.valuation L (algebraMap (𝓞 L) L b) = 1 := (w.valuation_eq_one_iff_notMem).mpr b.2
    rw [← hab, map_mul, h1, h3, mul_one] at h2
    exact lt_irrefl _ h2
  have := congrArg (fun t => A.valuation (i t)) hab
  simp only [map_mul] at this
  have hb' : A.valuation (i (algebraMap (𝓞 L) L b)) = 1 := hb
  rw [hb', mul_one] at this
  exact this.trans (hunit a ha)
end Formalism.BasicNotions.Examples₂.Tame
