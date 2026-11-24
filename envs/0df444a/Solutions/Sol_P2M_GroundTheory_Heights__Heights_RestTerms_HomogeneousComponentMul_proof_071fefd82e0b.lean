-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HomogeneousComponentMul_proof_071fefd82e0b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:21.806834+00:00
-- url     : https://prove2.me/submissions/7747f71e-f9fc-46a7-945c-259b7c86d688

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace HomogeneousComponentMul
theorem _root_.solution : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  have hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) =
      if d = m + i then p * homogeneousComponent i a else 0 := fun i =>
    homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))
  conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
  simp_rw [hterm]
  split_ifs with hmd
  · have hcongr : ∀ i ∈ range (a.totalDegree + 1),
        (if d = m + i then p * homogeneousComponent i a else 0) =
          if d - m = i then p * homogeneousComponent i a else 0 := by
      intro i _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
end HomogeneousComponentMul
end GroundTheory.Heights₂.Heights.RestTerms
