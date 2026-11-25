-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_finite_blockWeight_eq_7d351ef1e570
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:19.800814+00:00
-- url     : https://prove2.me/submissions/6f2c3c24-f7e7-4733-a43b-1a3562ab6d25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot

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
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun v : (Σ k, ι k) => m v.1)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_Iic]
  intro v
  have hcoord : (Finsupp.weight (blockWeight ι) d) v.1 =
      Finsupp.weight (fun x => blockWeight ι x v.1) d := by
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  have hle : d v ≤ Finsupp.weight (fun x => blockWeight ι x v.1) d :=
    Finsupp.le_weight _ (by simp [blockWeight]) d
  rw [← hcoord, hd] at hle
  simpa using hle
end GroundTheory.Heights₂.Heights.NumbersDVR
