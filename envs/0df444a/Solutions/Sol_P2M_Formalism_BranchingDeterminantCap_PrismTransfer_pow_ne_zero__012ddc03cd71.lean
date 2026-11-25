-- Prove2me | solution 1 for P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:28.457676+00:00
-- url     : https://prove2.me/submissions/8d5fff57-5968-4799-810a-943aacd9cd6c

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution (G : ℕ) (hG : 0 < G) : ((G : K) ^ 3) ≠ 0 := pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne')
end Formalism.BranchingDeterminantCap.PrismTransfer
