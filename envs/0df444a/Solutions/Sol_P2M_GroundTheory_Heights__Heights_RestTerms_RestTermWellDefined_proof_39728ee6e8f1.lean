-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestTermWellDefined_proof_39728ee6e8f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:26:11.070722+00:00
-- url     : https://prove2.me/submissions/31b6e50b-233c-499b-a610-1616ee41c206

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestTermWellDefined
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b


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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestTermWellDefined
theorem _root_.solution (h1 : LemmaA.Statement) : RestTermWellDefined.Statement := by
  intro f N F Q Q' hQ hQ' k hk1 hkN τ G hG
  obtain ⟨c, -, -, hA⟩ := h1 f N
  obtain ⟨P, hP, -, S, hS, hI⟩ := hA F Q hQ k hk1 hkN τ G hG
  obtain ⟨P', hP', -, S', hS', hI'⟩ := hA F Q' hQ' k hk1 hkN τ G hG
  have hPP : P = P' :=
    IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)) (hP.trans hP'.symm)
  have hSS : S = S' := Flag.powerSumHom_injective N (by rw [hS, hS', hPP])
  simp only [restTerm, hI, hI', hSS]
end RestTermWellDefined
end GroundTheory.Heights₂.Heights.RestTerms
