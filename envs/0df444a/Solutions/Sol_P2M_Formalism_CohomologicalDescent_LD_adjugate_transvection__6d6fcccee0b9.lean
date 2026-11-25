-- Prove2me | solution 1 for P2M_Formalism_CohomologicalDescent_LD_adjugate_transvection__6d6fcccee0b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:39.576527+00:00
-- url     : https://prove2.me/submissions/fac5c407-219a-42d3-a0fd-82d203780b64

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n] (i j : n)
    (h : i ≠ j) (c : S) : (Matrix.transvection i j c).adjugate = Matrix.transvection i j (-c) := by
  have h1 : Matrix.transvection i j c * Matrix.transvection i j (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection i j c).adjugate
      = (Matrix.transvection i j c).adjugate * (Matrix.transvection i j c * Matrix.transvection i j (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection i j (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne i j h, one_smul, Matrix.one_mul]
end Formalism.CohomologicalDescent.LD
