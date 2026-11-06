-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.card_generatedGroupElement_eq_two_pow_generatorRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:42:09.007706+00:00
-- url     : https://prove2.me/submissions/d74555dd-1302-4b76-838b-80f508d982bc

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Fintype.card P.code.1.GeneratedGroupElement = 2 ^ P.generatorRank := by
  letI : Fintype P.code.1.generatedVectorSubspace :=
    Fintype.ofEquiv P.code.1.GeneratedGroupElement P.generatedGroupElementVectorEquiv
  rw [Fintype.card_congr P.generatedGroupElementVectorEquiv]
  rw [Module.card_eq_pow_finrank (K := ZMod 2)
    (V := P.code.1.generatedVectorSubspace), ZMod.card]
  rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
