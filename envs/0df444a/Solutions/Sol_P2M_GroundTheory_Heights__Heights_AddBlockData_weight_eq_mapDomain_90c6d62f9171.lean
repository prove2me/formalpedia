-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:32:47.532853+00:00
-- url     : https://prove2.me/submissions/6d1c35d4-d631-40df-8c2f-def957728f17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution (s : Coord D.extSizes →₀ ℕ) :
    ⇑(s.mapDomain Sigma.fst) = Finsupp.weight (coordDeg D.extSizes) s := by
  funext o
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finsupp.finsetSum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finsupp.single_apply, Pi.smul_apply, coordDeg, Pi.single_apply, smul_eq_mul]
  by_cases h : v.1 = o
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
end GroundTheory.Heights₂.Heights.AddBlockData
