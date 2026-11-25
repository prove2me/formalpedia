-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_integral_primitive_79d7c8a66779
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:16.817948+00:00
-- url     : https://prove2.me/submissions/28819aed-2353-4707-9304-20f5441d536e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_GenericPrimitive_proof_eb00a83c5a8e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]
omit [IsDomain R] [IsDomain A]
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution [FaithfulSMul R A] [Algebra.IsAlgebraic R A] {n : ℕ} (x : Fin n → A)
    (hgen : IntermediateField.adjoin E (Set.range fun j => algebraMap A L (x j)) = ⊤) :
    ∃ θ : A, IsIntegral R θ ∧ IntermediateField.adjoin E {algebraMap A L θ} = ⊤ := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap E L).injective
  have hint : ∀ j, IsIntegral E (algebraMap A L (x j)) := fun j =>
    (((Algebra.IsAlgebraic.isAlgebraic (R := R) (x j)).algHom (IsScalarTower.toAlgHom R A L)).extendScalars
      (IsFractionRing.injective R E)).isIntegral
  have : FiniteDimensional E L := by
    have := IntermediateField.finiteDimensional_adjoin (K := E)
      (S := Set.range fun j => algebraMap A L (x j)) (by rintro _ ⟨j, rfl⟩; exact hint j)
    rw [hgen] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable E L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ E) q, map_ratCast, eq_ratCast]
  obtain ⟨D, hD, hDc⟩ := ComplexSets.GenericPrimitive.proof ℚ E L n (fun j => algebraMap A L (x j)) hgen
  obtain ⟨c, hc, hcD⟩ : ∃ c ∈ Set.pi Set.univ (fun _ : Fin n => Set.range (Int.cast : ℤ → ℚ)),
      MvPolynomial.eval c D ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (MvPolynomial.funext_set _ (fun _ => Set.infinite_range_of_injective Int.cast_injective)
      fun c hc => by simpa using h c hc)
  choose z hz using fun j => hc j (Set.mem_univ j)
  set θ₁ : A := ∑ j, z j • x j with hθ₁def
  have hθ₁ : IntermediateField.adjoin E {algebraMap A L θ₁} = ⊤ := by
    have h := hDc c hcD
    have he : ∑ j, c j • algebraMap A L (x j) = algebraMap A L θ₁ := by
      simp only [hθ₁def, map_sum, map_zsmul, ← hz, Int.cast_smul_eq_zsmul]
    rwa [he] at h
  obtain ⟨a, ha, hai⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) θ₁).exists_integral_multiple
  refine ⟨a • θ₁, hai, eq_top_iff.2 (hθ₁ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)⟩
  have ha' : algebraMap E L (algebraMap R E a) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L]
    intro h0
    exact ha ((FaithfulSMul.algebraMap_injective R A).eq_iff' (map_zero _) |>.1
      ((IsFractionRing.injective A L).eq_iff' (map_zero _) |>.1 h0))
  have heq : algebraMap A L θ₁ = (algebraMap E L (algebraMap R E a))⁻¹ * algebraMap A L (a • θ₁) := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L,
      IsScalarTower.algebraMap_apply R E L, inv_mul_cancel_left₀ ha']
  rw [heq]
  exact mul_mem (IntermediateField.inv_mem _ (IntermediateField.algebraMap_mem _ _))
    (IntermediateField.mem_adjoin_simple_self E _)
end GroundTheory.Heights₂.Heights.HypersurfacePresentation
