-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_exists_zsmul_mem_dualLattice_a99542587a2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:49.341336+00:00
-- url     : https://prove2.me/submissions/ce4f4842-6244-41d3-aaa9-4133e9b867aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective

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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.DualEmbeddingBijective
theorem _root_.solution (F : HermLattice K i) (y : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • y ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image y ∪ S.biUnion fun g => Finset.univ.image g)
  have hint : ∀ z : K, IsIntegral ℤ z → z ∈ (algebraMap (𝓞 K) K).range :=
    fun z hz => ⟨⟨z, hz⟩, rfl⟩
  refine ⟨d * d, mul_ne_zero hd0 hd0, ?_⟩
  intro x hx
  rw [← hS] at hx
  refine Submodule.span_induction
    (p := fun x _ => ((d * d) • y) ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range) ?_ ?_ ?_ ?_ hx
  · intro g hg
    have hsum : ((d * d) • y) ⬝ᵥ g = ∑ j, (d • y j) * (d • g j) := by
      simp only [dotProduct, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    refine sum_mem fun j _ => mul_mem (hint _ (hd _ ?_)) (hint _ (hd _ ?_))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨g, Finset.mem_coe.mp hg, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
  · rw [dotProduct_zero]
    exact zero_mem _
  · intro x z _ _ hx hz
    rw [dotProduct_add]
    exact add_mem hx hz
  · intro a x _ hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [dotProduct_smul, map_mul, hc]; rfl⟩
end GroundTheory.Heights₂.Heights.DualEmbeddingBijective
