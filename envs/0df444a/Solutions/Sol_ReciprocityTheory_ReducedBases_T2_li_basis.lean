-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.li_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:44.100449+00:00
-- url     : https://prove2.me/submissions/9dd560b5-ac2b-4370-b6e1-28d6db8cc33d

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_apply
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_eq_TB
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_expand
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_TB_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    LinearIndependent ℝ (fun i => fB 1 (e i)) ∧ LinearIndependent ℝ (fun i => fB B (e i)) := by
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range fun i => fB 1 (e i)) := by
    rw [← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis j = fB 1 (Pi.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [fB_apply, toReal]
      · simp [fB_apply, toReal, hk]
    rw [SetLike.mem_coe, hj, fB_expand 1 e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 : LinearIndependent ℝ (fun i => fB 1 (e i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  refine ⟨h1, ?_⟩
  have h2 := h1.map' (TB B) (LinearMap.ker_eq_bot.2 (TB_injective A B hA hAB))
  have hfun : (fun i => fB B (e i)) = (TB B) ∘ (fun i => fB 1 (e i)) := by
    funext i
    exact fB_eq_TB B (e i)
  rw [hfun]
  exact h2
end ReciprocityTheory.ReducedBases.T2
