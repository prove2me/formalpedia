-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:07.65524+00:00
-- url     : https://prove2.me/submissions/0b142e47-f846-4311-9c73-8fb63471cbe4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {E V : Type*} [TopologicalSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : E → ℂ) (a : E → V) :
    tsupport (fun x => φ x • a x) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h; apply hx; simp [h]
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
