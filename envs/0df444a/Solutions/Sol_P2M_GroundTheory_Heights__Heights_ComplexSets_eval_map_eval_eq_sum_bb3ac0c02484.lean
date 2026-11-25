-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_eval_map_eval_eq_sum_bb3ac0c02484
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:43.779446+00:00
-- url     : https://prove2.me/submissions/8e6f9c6e-8690-42b7-ad31-a5869d180eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSimpleRootBranch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    (p.map (MvPolynomial.eval w)).eval s =
      ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval w (p.coeff i) * s ^ i := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]
end GroundTheory.Heights₂.Heights.ComplexSets
