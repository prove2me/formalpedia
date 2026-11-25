-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.exists_basis_map_restrictToSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:47.209674+00:00
-- url     : https://prove2.me/submissions/6612d215-2006-464a-b8f3-85d167039948

import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_matrix_span_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]
    rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩
end ReciprocityTheory.PGsh.L2
