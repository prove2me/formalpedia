-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.actual_Y_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:20:53.44651+00:00
-- url     : https://prove2.me/submissions/46ee8766-9928-452d-9045-53defdbc18ee

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
theorem _root_.solution (S : OddScale) (n : Nat) (q : Physical S (n + 2)) :
    CSSDaviesLocality.coupling q .y = Complex.I •
      (Semantics.Qubit.localX q * Semantics.Qubit.localZ q) :=
  CSSDaviesLocality.coupling_y q
end QEC.Coding.BDL26TransposedStoppedDecoder
