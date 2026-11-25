-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:00.217817+00:00
-- url     : https://prove2.me/submissions/44d5424f-9a9a-4d7f-b1fc-8a9e90627aca

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hs)]
end Formalism.FourierDecayAlt.P.PBK
