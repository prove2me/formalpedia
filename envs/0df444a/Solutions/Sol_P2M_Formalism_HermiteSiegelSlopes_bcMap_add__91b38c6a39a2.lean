-- Prove2me | solution 1 for P2M_Formalism_HermiteSiegelSlopes_bcMap_add__91b38c6a39a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:57.381055+00:00
-- url     : https://prove2.me/submissions/cc8236d3-7acb-46f0-8e3d-e40fa8bdf29c

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (x y : ι → F) : bcMap (E := E) (x + y) = bcMap x + bcMap y := by
  funext i
  simp [bcMap]
end Formalism.HermiteSiegelSlopes
