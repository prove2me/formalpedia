-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:04.752974+00:00
-- url     : https://prove2.me/submissions/8444913c-18ad-4dd8-8748-98c40f5ed55f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution (g : Matrix ι κ K) : 0 ≤ sz g := Real.iSup_nonneg fun _ => norm_nonneg _
end GlobalTheory.CompanionTheory.Wedge
