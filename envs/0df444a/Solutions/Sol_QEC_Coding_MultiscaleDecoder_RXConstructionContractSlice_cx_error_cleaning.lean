-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice.cx_error_cleaning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:47:03.025243+00:00
-- url     : https://prove2.me/submissions/b82adf28-1893-4b4e-93c1-a51f467cb95d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a b c
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
namespace QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice
theorem _root_.solution
    (K : RXConstructionContractSlice (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
    (x : X) (error : D.family.Cochain1 i.succ)
    (hcocycle : K.rx_local_complexes.cxDelta1 x
        (restrictWordLinear (Lx.correctionRegion x) error) = 0) :
    ∃ stabilizer : Word BDL26Field (X0 x),
      restrictWordLinear (Lx.correctionRegion x)
        (error + D.family.coboundary0 i.succ
          (K.support_decomposition.cxLift0 x stabilizer)) = 0 := by
  have hmem : restrictWordLinear (Lx.correctionRegion x) error ∈
      LinearMap.ker (K.rx_local_complexes.cxDelta1 x) := hcocycle
  rw [K.rx_local_cohomology.cx_h1_ker_eq_range x] at hmem
  rcases hmem with ⟨stabilizer, hstabilizer⟩
  refine ⟨stabilizer, ?_⟩
  rw [map_add, K.support_decomposition.cxDelta0_restriction, hstabilizer]
  ext j
  exact ZModModule.add_self _
end QEC.Coding.MultiscaleDecoder.RXConstructionContractSlice
