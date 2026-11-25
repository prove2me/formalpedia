-- Prove2me | solution 1 for PI.Dv.RK.eG_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:07.742108+00:00
-- url     : https://prove2.me/submissions/0d82f5f5-40f7-40a9-a085-8135d40f7a1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
import Theorems.Thm_PI_Dv_RK_mul_eS
import Theorems.Thm_PI_Dv_RK_end_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.RK
theorem _root_.solution (T : GoodSet K G) (P : Pair K G) (h : ∀ s, (T.tau s).asAlgebraHom (eps P) ≠ 0) :
    eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P * b} := by
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  obtain ⟨n, A, B, hAB⟩ := end_simple _ (h s)
  choose a ha using fun i => T.irr s (A i)
  choose b hb using fun i => T.irr s (B i)
  have hτ : (T.tau s).asAlgebraHom (∑ i, a i * eps P * b i) = (T.tau s).asAlgebraHom 1 := by
    rw [map_one, map_sum]
    simp only [map_mul, ha, hb]
    exact hAB
  have e1 := mul_eS T s (∑ i, a i * eps P * b i)
  have e2 := mul_eS T s 1
  rw [one_mul] at e2
  have key : (∑ i, a i * eps P * b i) * eS T s = eS T s := by
    rw [e1, e2, hτ]
  rw [← key, Finset.sum_mul]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨a i, b i * eS T s, mul_assoc _ _ _⟩
end PI.Dv.RK
