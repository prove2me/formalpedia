-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.basisTranslations_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:48:33.946819+00:00
-- url     : https://prove2.me/submissions/37d22ec7-cf70-4515-8072-0cc319e9777e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) :
    (basisTranslations S n u v q .y).1.val = u.val + zSyndrome S (n + 2) (Pi.single q 1) ∧
    (basisTranslations S n u v q .y).2.val = v.val + xSyndrome S (n + 2) (Pi.single q 1) := by
  exact ⟨rfl,rfl⟩
end QEC.Coding.BDL26TransposedStoppedDecoder
