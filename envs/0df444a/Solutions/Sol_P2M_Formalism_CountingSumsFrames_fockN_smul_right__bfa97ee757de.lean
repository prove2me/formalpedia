-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:02.75241+00:00
-- url     : https://prove2.me/submissions/908c76a1-e109-44e5-88ad-069fbec54762

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} (LL : Letters N) (c : ℚ_[p]) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fockN p LL F (c • G) = c * fockN p LL F G := by
  unfold fockN
  rw [fock_smul_right, mul_div_assoc]
end Formalism.CountingSumsFrames
