-- Prove2me | solution 1 for Section5DecoderLayout.records_columnLabel
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:00.002408+00:00
-- url     : https://prove2.me/submissions/ab44ed1a-a007-4348-b7fd-bb1d6b51c5a9

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
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Section5DecoderLayout

@[simp] theorem records_score {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (scoreWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (scoreField N b i)=scores j i := by
  change records j (Fin.castAdd _ i)=_
  exact combineEmb_castAdd _ _ _ i

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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution {N K b f : ℕ} (j : Fin (N+1)) (e : Fin (Section5DecoderLayout.recordWidth N b)) :
    Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.records j e))=some j := by
  induction e using Fin.addCases with
  | left e =>
    change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.records j (Section5DecoderLayout.scoreField N b e)))=_
    rw [Section5DecoderLayout.records_score]
    change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.code N K b f (Section5DecoderLayout.Wire.score j e)))=_
    rw [Equiv.symm_apply_apply]
    rfl
  | right e =>
    induction e using Fin.addCases with
    | left e =>
      change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.records j (Section5DecoderLayout.realField N b e)))=_
      rw [Section5DecoderLayout.records_real]
      change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.code N K b f
        (Section5DecoderLayout.Wire.matrix (Fin.last K) ((section5_complex_entry_index (N+1)).symm
          (false,(finProdFinEquiv.symm e).1,j)) (finProdFinEquiv.symm e).2)))=_
      rw [Equiv.symm_apply_apply]
      simp only [Section5DecoderLayout.columnLabel,Equiv.apply_symm_apply]
    | right e =>
      change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.records j (Section5DecoderLayout.imagField N b e)))=_
      rw [Section5DecoderLayout.records_imag]
      change Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.code N K b f
        (Section5DecoderLayout.Wire.matrix (Fin.last K) ((section5_complex_entry_index (N+1)).symm
          (true,(finProdFinEquiv.symm e).1,j)) (finProdFinEquiv.symm e).2)))=_
      rw [Equiv.symm_apply_apply]
      simp only [Section5DecoderLayout.columnLabel,Equiv.apply_symm_apply]
