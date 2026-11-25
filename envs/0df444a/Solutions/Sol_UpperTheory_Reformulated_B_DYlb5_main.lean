-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYlb5.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:10.622383+00:00
-- url     : https://prove2.me/submissions/105d6ff9-8224-4fe2-a379-9db55cc83085

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYlb5
theorem _root_.solution :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (f : Module.Dual k (Matrix (Fin n) (Fin n) k)), Continuous (⇑f : Matrix (Fin n) (Fin n) k → k) := by
  intro k _ _ _ _ n f
  haveI : IsTopologicalRing k := inferInstance
  have key : ∀ M : Matrix (Fin n) (Fin n) k,
      f M = ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
      simp [Matrix.smul_single]
    rw [this, map_smul, smul_eq_mul]
  have : (⇑f : Matrix (Fin n) (Fin n) k → k) =
      fun M => ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := funext key
  rw [this]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).mul continuous_const
end UpperTheory.Reformulated.B.DYlb5
