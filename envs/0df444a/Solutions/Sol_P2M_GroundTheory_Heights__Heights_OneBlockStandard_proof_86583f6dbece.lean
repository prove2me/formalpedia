-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockStandard_proof_86583f6dbece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:46.553248+00:00
-- url     : https://prove2.me/submissions/79527cc4-09e0-4541-b5f0-a4eef0063e7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_oneBlockForms_linearIndependent_f83fe6e1b7c6

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
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
namespace OneBlockStandard
theorem _root_.solution : OneBlockStandard.Statement := by
  intro K _ _ e r om
  refine ⟨⟨oneBlockForms_linearIndependent om, le_antisymm ?_ ?_⟩, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩ v hv
    obtain ⟨b, hb⟩ := standard_coord_integral hv (oneBlockIndex e r p).2
    refine ⟨om (oneBlockIndex e r p).1 * b, ?_⟩
    simp only [oneBlockForms, single_dotProduct, map_mul, hb]
  · intro ψ hψ
    have hj : ∀ j, ∃ b : 𝓞 K, ψ j = algebraMap (𝓞 K) K b := by
      intro j
      obtain ⟨b, hb⟩ := hψ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨b, by rw [hb, dotProduct_single, mul_one]⟩
    choose b hb using hj
    have hsum : ψ = ∑ j, ∑ a, om.repr (b j) a •
        oneBlockForms (r := r) om ((oneBlockIndex e r).symm (a, j)) := by
      funext i
      simp only [oneBlockForms_symm_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        smul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hb i]
      conv_lhs => rw [← om.sum_repr (b i)]
      push_cast
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.sum_mem _ fun a _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hmap : latticeMap (oneBlockForms (r := r) om) = oneBlockMap om := by
      apply MvPolynomial.ringHom_ext
      · intro n
        simp [latticeMap, oneBlockMap]
      · intro v
        simp only [latticeMap, oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms, latticeForm]
        rw [Finset.sum_eq_single (oneBlockIndex e r v.2).2]
        · simp
        · intro i _ hi
          simp [hi]
        · simp
    unfold latticeIdeal oneBlockIdeal
    rw [hmap]
  · intro σ w
    funext _ p
    simp only [latticePoint, oneBlockPoint, oneBlockForms]
    rw [Finset.sum_eq_single (oneBlockIndex e r p).2]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
end OneBlockStandard
end GroundTheory.Heights₂.Heights
