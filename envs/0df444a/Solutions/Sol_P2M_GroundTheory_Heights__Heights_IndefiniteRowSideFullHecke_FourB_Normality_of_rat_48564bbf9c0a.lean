-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_Normality_of_rat_48564bbf9c0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:18.177235+00:00
-- url     : https://prove2.me/submissions/ef14e941-2afe-499a-8844-701dc93a1a4c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace Normality
theorem _root_.solution (hA : IntegralOnModelRat) : Normality.Statement := by
  intro A _ h a N ⟨hft, hdom, hic, htf, hh, hN, hint⟩
  let _ : Algebra (𝓞 ℚ) A :=
    ((Int.castRingHom A).comp (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).toAlgebra
  have : IsDomain A := hdom
  have : Algebra.FiniteType (𝓞 ℚ) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 ℚ) A
  have hmap : ∀ c : 𝓞 ℚ, c ≠ 0 → algebraMap (𝓞 ℚ) A c ≠ 0 := fun c hc =>
    htf _ fun h0 => hc (Rat.ringOfIntegersEquiv.injective (by simpa using h0))
  have : Module.IsTorsionFree (𝓞 ℚ) A := ⟨fun c hc x y hxy => by
    have hc0 : c ≠ 0 := hc.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (hmap c hc0) hxy⟩
  have hNQ : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  suffices hH : FourB.IntegralOnModel.Hyp ℚ A a h (N : 𝓞 ℚ) by
    obtain ⟨r', hr'⟩ := hA A a h (N : 𝓞 ℚ) hH
    exact ⟨r', by rw [hr', map_natCast]⟩
  refine ⟨hNQ, hh, fun v L _ _ _ y _ hyint hyg => ?_⟩
  let P := primesEquiv v
  have : Fact (P : ℕ).Prime := ⟨P.2⟩
  let e : ℚ_[P] ≃+* v.adicCompletion ℚ := (adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv
  let _ : Algebra ℚ_[P] L :=
    ((algebraMap (v.adicCompletion ℚ) L).comp (e : ℚ_[P] →+* v.adicCompletion ℚ)).toAlgebra
  have : FiniteDimensional ℚ_[P] L := finiteDimensional_of_ringEquiv e rfl
  have : Algebra.IsAlgebraic ℚ_[P] L := inferInstance
  let _ : NormedField L := spectralNorm.normedField ℚ_[P] L
  let _ : NormedAlgebra ℚ_[P] L := spectralNorm.normedAlgebra ℚ_[P] L
  have key : ∀ x : L, ‖x‖ ≤ 1 ↔ ((algebraMap (v.adicCompletion ℚ) L).comp
      (v.adicCompletionIntegers ℚ).subtype).IsIntegralElem x := fun x =>
    norm_le_one_iff_isIntegralElem_of_equiv (P : ℕ) (v.adicCompletionIntegers ℚ).subtype
      (e : ℚ_[P] →+* v.adicCompletion ℚ) (adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv
      (fun z => adicCompletionIntegers.coe_padicIntEquiv_symm_apply v z) rfl x
  have hle := hint (P : ℕ) L y (fun b => (key _).2 (hyint b)) hyg
  rw [← key, map_natCast, map_natCast, norm_div]
  have hpos : 0 < ‖(N : L)‖ := by
    rw [← map_natCast (algebraMap ℚ_[P] L), norm_algebraMap', norm_pos_iff]
    exact_mod_cast hN.ne'
  exact (div_le_one hpos).2 hle
end Normality
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
