-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthTransverseSlice_proof_e3d65b90a303
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:36.385248+00:00
-- url     : https://prove2.me/submissions/b192e8f6-e49d-4de3-b607-9314b21a0ce9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthTransverseSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalDimDomain_proof_aafc8deef599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385


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
open MvPolynomial Matrix ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace LengthTransverseSlice
theorem _root_.solution (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) : LengthTransverseSlice.Statement := by
  intro n d I W q L hW hdim hq huniq hCMq hT
  have hWp : W.IsPrime := hW.1.1
  have hWm : W ≤ RingHom.ker (eval q) := fun f hf => RingHom.mem_ker.2 (hq f hf)
  have : IsCohenMacaulayLocalRing (localRingAt I q) := hCMq
  have h := length_slice_of_isCohenMacaulay hCM hLS (RingHom.ker (eval q)) W I hW hWm
    (fun W' hW' hle => huniq W' hW' fun f hf => RingHom.mem_ker.1 (hle hf)) d
    (fun i => linPoly L i - C ((L *ᵥ q) i))
    (fun i => by rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self])
    (LocalDimDomain.proof n d W hWp hdim q hq)
    (fun g hg => by
      obtain ⟨s, hs, hsg⟩ := hT g (RingHom.mem_ker.1 hg)
      exact ⟨s, fun h => hs (RingHom.mem_ker.1 h), hsg⟩)
  unfold localMult
  rw [dif_pos hWp, dif_pos (inferInstance : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime), h]
  rfl
end LengthTransverseSlice
end GroundTheory.Heights₂.Heights
