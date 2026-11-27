-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocFrac_proof_52da8c49b8a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:10.55431+00:00
-- url     : https://prove2.me/submissions/aca766bc-2975-44a0-8fa0-f080595fe96b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocFrac
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DegZeroLocFrac
theorem _root_.solution : DegZeroLocFrac.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro x hx

  let E : IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
    { carrier := {x | ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * y₂, Subalgebra.mul_mem _ hy₁ hy₂, z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂,
          mul_ne_zero hz₁0 hz₂0, by rw [div_mul_div_comm]⟩
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * z₂ + z₁ * y₂,
          Subalgebra.add_mem _ (Subalgebra.mul_mem _ hy₁ hz₂) (Subalgebra.mul_mem _ hz₁ hy₂),
          z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_ne_zero hz₁0 hz₂0,
          by rw [div_add_div _ _ hz₁0 hz₂0]⟩
      algebraMap_mem' := fun c => ⟨algebraMap F _ c, Subalgebra.algebraMap_mem _ c, 1,
        Subalgebra.one_mem _, one_ne_zero, (div_one _).symm⟩
      inv_mem' := by
        rintro _ ⟨y, hy, z, hz, hz0, rfl⟩
        by_cases hy0 : y = 0
        · exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by simp [hy0]⟩
        · exact ⟨z, hz, y, hy, hy0, by rw [inv_div]⟩ }
  suffices hle : homFracDegZero P ≤ E from hle hx
  unfold homFracDegZero
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩

  obtain ⟨e, h, hh, hbe, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := h𝒲P W (h𝒲.mem_toFinset.mp hW)
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) b
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmP⟩ := exists_form_not_mem_of_isRelevant (H := P) hP.relevant (e - b)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    div_ne_zero (hq0 _ fun h' => (hP.isPrime.mem_or_mem h').elim hgP hmP) (hq0 _ hhP), ?_⟩
  simp only [map_mul]
  rw [div_div_div_cancel_right₀ (hq0 _ hhP), mul_div_mul_right _ _ (hq0 _ hmP)]
end DegZeroLocFrac
end GroundTheory.Heights₂.Heights.FieldNumbers
