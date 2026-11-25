-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_setOf_weight_blockWeight_eq_d003e8a029f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:54.488957+00:00
-- url     : https://prove2.me/submissions/904c1497-61ed-4aac-b306-c0ca32d21395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  refine ((Set.Finite.pi' fun v : (Σ k, ι k) => Set.finite_le_nat (m v.1)).preimage
    DFunLike.coe_injective.injOn).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro v
  rw [← hd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun u => (d u • blockWeight ι u) v.1) (fun _ _ => Nat.zero_le _) hv)
    simp [blockWeight]
  · simp [Finsupp.notMem_support_iff.mp hv]
end GroundTheory.Heights₂.Heights.NumbersDVR
