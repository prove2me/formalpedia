-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:46:10.686116+00:00
-- url     : https://prove2.me/submissions/4ffac0db-b2ed-467a-b303-f33840b9066d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableLinear_actual
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toExecutableSyndrome_injective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=
      tannerCoboundary1 (levelTwoPresentation S) a := by
  apply toExecutableSyndrome_injective S
  have hp : executableSyndrome S (executableGlobal S (toExecutableSyndrome S
      (tannerCoboundary1 (levelTwoPresentation S) a)))=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a) :=
    global_preimage (executableLinear S) _ ⟨toExecutableError S a,
      executableLinear_actual S a⟩
  have he : toExecutableError S (actualGlobal S
      (tannerCoboundary1 (levelTwoPresentation S) a))=
      executableGlobal S (toExecutableSyndrome S
        (tannerCoboundary1 (levelTwoPresentation S) a)) :=
    toExecutableError_toActualError S _
  exact (executableSyndrome_eq S (actualGlobal S
    (tannerCoboundary1 (levelTwoPresentation S) a))).symm.trans
      ((congrArg (executableSyndrome S) he).trans hp)
end QEC.Coding.BDL26GlobalLookupLinearity
