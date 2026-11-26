-- Prove2me | solution 1 for Section5DecoderLayout.record_matrix_read
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:01.104538+00:00
-- url     : https://prove2.me/submissions/1958e36d-124d-4285-a3fc-58502b9a01a3

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Section5DecoderLayout



































@[simp] theorem part_on {N K b f : ℕ} (imaginary : Bool) (j i : Fin (N+1)) (e : Fin (b+1)) :
    part (K:=K) (f:=f) imaginary j (finProdFinEquiv (i,e))=
      matrix (f:=f) (Fin.last K) ((section5_complex_entry_index (N+1)).symm (imaginary,i,j)) e := by
  change code N K b f (Wire.matrix (Fin.last K)
    ((section5_complex_entry_index (N+1)).symm
      (imaginary,(finProdFinEquiv.symm (finProdFinEquiv (i,e))).1,j))
    (finProdFinEquiv.symm (finProdFinEquiv (i,e))).2)=_
  rw [Equiv.symm_apply_apply]
  rfl













end Section5DecoderLayout

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Section5DecoderLayout



@[simp] theorem records_real {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (payloadWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (realField N b i)=part false j i := by
  change records j (Fin.natAdd _ (Fin.castAdd _ i))=_
  unfold records
  rw [combineEmb_natAdd,combineEmb_castAdd]

@[simp] theorem records_imag {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (payloadWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (imagField N b i)=part true j i := by
  change records j (Fin.natAdd _ (Fin.natAdd _ i))=_
  unfold records
  rw [combineEmb_natAdd,combineEmb_natAdd]













end Section5DecoderLayout

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Final signed decoding of the fixed-width matrix-power circuit. The register
width is linear in the number of products and the input/dimension bit bounds. -/

@[ext] theorem Section5IntegerMatrix.ext {n : ℕ} {A B : Section5IntegerMatrix n}
    (hre : A.re=B.re) (him : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hre
  cases him
  rfl









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution {N K b f : ℕ} (z : Qubits (Section5DecoderLayout.width N K b f)) :
    section5_record_integer_matrix Section5DecoderLayout.records (Section5DecoderLayout.realField N b) (Section5DecoderLayout.imagField N b) z=
      section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) (Fin.last K)) z := by
  apply Section5IntegerMatrix.ext <;> funext i j
  · change section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z (Section5DecoderLayout.records j (Section5DecoderLayout.realField N b (finProdFinEquiv (i,e)))))=_
    simp only [Section5DecoderLayout.records_real,Section5DecoderLayout.part_on,section5_signed_matrix_read,Function.comp_def]
  · change section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z (Section5DecoderLayout.records j (Section5DecoderLayout.imagField N b (finProdFinEquiv (i,e)))))=_
    simp only [Section5DecoderLayout.records_imag,Section5DecoderLayout.part_on,section5_signed_matrix_read,Function.comp_def]
