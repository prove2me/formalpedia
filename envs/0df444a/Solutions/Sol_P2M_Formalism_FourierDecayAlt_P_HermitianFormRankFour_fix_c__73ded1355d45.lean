-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_HermitianFormRankFour_fix_c__73ded1355d45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:10.94318+00:00
-- url     : https://prove2.me/submissions/89389e13-0a84-4ee6-b3b2-0df0640fc779

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (j : JJ r) :
    h *ᵥ cvec' k r z j = cvec' k r z j := by
  obtain ⟨_, he, hz⟩ := hh
  rcases j with a | a | u
  · exact (he a).2
  · exact (he a).1
  · simp only [cvec']
    rw [mulVec_smul, hz]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
