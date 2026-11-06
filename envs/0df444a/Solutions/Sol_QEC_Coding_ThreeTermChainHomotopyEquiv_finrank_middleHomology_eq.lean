-- Prove2me | solution 1 for QEC.Coding.ThreeTermChainHomotopyEquiv.finrank_middleHomology_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:32:05.480603+00:00
-- url     : https://prove2.me/submissions/8473c26b-4dc5-43fb-b991-f7ad7b2ce0a0

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy

set_option autoImplicit false
open QEC QEC.Coding
universe u v w z
variable {F : Type u} [Field F]
variable {A0 A1 A2 : Type v}
variable {B0 B1 B2 : Type w}
variable {C0 C1 C2 : Type z}
variable [AddCommGroup A0] [Module F A0]
variable [AddCommGroup A1] [Module F A1]
variable [AddCommGroup A2] [Module F A2]
variable [AddCommGroup B0] [Module F B0]
variable [AddCommGroup B1] [Module F B1]
variable [AddCommGroup B2] [Module F B2]
variable [AddCommGroup C0] [Module F C0]
variable [AddCommGroup C1] [Module F C1]
variable [AddCommGroup C2] [Module F C2]
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable [Fintype F]
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {A0 A2 : Type (max u v)} [AddCommGroup A0] [Module F A0]
  [AddCommGroup A2] [Module F A2]
variable {B0 B2 : Type (max u w)} [AddCommGroup B0] [Module F B0]
  [AddCommGroup B2] [Module F B2]
variable {A : ChainComplexData F A0 (Word F ι) A2}
variable {B : ChainComplexData F B0 (Word F κ) B2}
namespace QEC.Coding.ThreeTermChainHomotopyEquiv
theorem _root_.solution
    (e : ThreeTermChainHomotopyEquiv A B) :
    Module.finrank F A.middleHomology =
      Module.finrank F B.middleHomology :=
  e.inducedMiddleHomologyEquiv.finrank_eq
end QEC.Coding.ThreeTermChainHomotopyEquiv
