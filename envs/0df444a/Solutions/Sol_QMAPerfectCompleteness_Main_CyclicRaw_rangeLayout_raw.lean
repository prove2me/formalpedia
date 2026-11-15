-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRaw.rangeLayout_raw
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:52:58.839488+00:00
-- url     : https://prove2.me/submissions/07cd7211-80a1-46a7-957d-f1361a19eca0

/- Generated from Solutions.CyclicRawCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect

/- Inline helpers retained from Solutions.DynamicRangeLayout. -/
section


/-! Disjoint source/scratch register constructors for the dynamic range comparator scaffold. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open VariableComparison





namespace RangeWires
variable {n r : ℕ} (W : RangeWires n r)



lemma comparator_left (t : Fin 3) (i : Fin r) : leftWire (W.comparator t) i = W.index i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.castAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_left]

lemma comparator_right (t : Fin 3) (i : Fin r) : rightWire (W.comparator t) i = W.thresholds t i := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨r+i.val,by have := i.isLt; omega⟩) =
      Fin.castAdd (r+2) (Fin.natAdd r i) := Fin.ext rfl
  rw [he,Fin.append_left,Fin.append_right]

lemma comparator_carry (t : Fin 3) (i : Fin (r+1)) :
    carryWire (W.comparator t) i = W.scratch (Fin.castAdd 1 i) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨2*r+i.val,by have := i.isLt; omega⟩) =
      Fin.natAdd (r+r) (Fin.castAdd 1 i) := Fin.ext (by
        change 2*r+i.val = r+r+i.val
        omega)
  rw [he,Fin.append_right]

lemma comparator_temp (t : Fin 3) : tempWire (W.comparator t) = W.scratch (Fin.last (r+1)) := by
  change Fin.append (Fin.append W.index (W.thresholds t)) W.scratch
    (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) = _
  have he : (Fin.cast (by omega : 3*r+2 = (r+r)+(r+2)) ⟨3*r+1,by omega⟩) =
      Fin.natAdd (r+r) (Fin.last (r+1)) := Fin.ext (by simp; omega)
  rw [he,Fin.append_right]







end RangeWires
end QMAPerfectCompleteness.Main.DynamicBlockCompiler

end

/- Inline helpers retained from Solutions.CyclicRawLayout. -/
section


/-! Executable scalar metadata and affine physical addresses for the actual cyclic compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding CertificateMasterLayout





namespace Meta



































end Meta











@[simp] theorem r_meta (V : Verifier gatesG2) : (params V).r=r V := by simp only [params,ofRaw_erase]; rfl
@[simp] theorem oldWork_meta (V : Verifier gatesG2) : (params V).oldWork=oldWork V := by simp only [params,ofRaw_erase]; rfl


@[simp] theorem body_meta (V : Verifier gatesG2) : (params V).body=BlockCircuit.bodyWires V := by simp only [params,ofRaw_erase]; rfl





@[simp] theorem word_meta (V : Verifier gatesG2) (d : Fin 6) (j : Fin (r V)) :
    (prepWord V d j).val=(params V).word d.val j.val := by
  change BlockCircuit.bodyWires V+oldWork V+(j.val+r V*d.val) =
    (params V).body+(params V).oldWork+(d.val*(params V).r+j.val)
  rw [body_meta,oldWork_meta,r_meta]
  ac_rfl










end QMAPerfectCompleteness.Main.CyclicRaw

end



/-! Literal raw-code correspondence for the coherent certificate compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace QMAPerfectCompleteness.Main.CyclicRaw
end QMAPerfectCompleteness.Main.CyclicRaw
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding RawG2 CertificateMasterLayout


@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.params_eq_source (V : Verifier gatesG2) : params V=sourceMeta V := ofRaw_erase V



@[ext] theorem QMAPerfectCompleteness.Main.CyclicRaw.borrow_ext {r : ℕ} (L M : RawG2.BorrowLayout r)
    (ha : ∀j,L.left j=M.left j) (hb : ∀j,L.right j=M.right j)
    (hc : ∀j,L.carry j=M.carry j) (hp : L.temp=M.temp) : L=M := by
  cases L; cases M
  simp only [BorrowLayout.mk.injEq]
  exact ⟨funext ha,funext hb,funext hc,hp⟩

@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.source_word (V : Verifier gatesG2) (d : Fin 6) (j : Fin (r V)) :
    (prepWord V d j).val=(sourceMeta V).word d.val j.val := by
  simpa only [params_eq_source] using word_meta V d j






@[simp] theorem QMAPerfectCompleteness.Main.CyclicRaw.erase_wires_comparator {n r : ℕ} (W : DynamicBlockCompiler.RangeWires n r) (d : Fin 3) :
    eraseBorrow (W.comparator d)=
      ⟨fun j=>(W.index j).val,fun j=>(W.thresholds d j).val,
        fun j=>(W.scratch (Fin.castAdd 1 j)).val,(W.scratch (Fin.last (r+1))).val⟩ := by
  apply borrow_ext
  · intro j; exact congrArg Fin.val (W.comparator_left d j)
  · intro j; exact congrArg Fin.val (W.comparator_right d j)
  · intro j; exact congrArg Fin.val (W.comparator_carry d j)
  · exact congrArg Fin.val (W.comparator_temp d)

@[simp] theorem solution (V : Verifier gatesG2) :
    eraseRange (CertificateRangeCircuit.layout V)=(sourceMeta V).ranges := by
  change RangeLayout.mk _ _ = RangeLayout.mk _ _
  congr 1
  funext d
  change eraseBorrow ((CertificateRangeCircuit.wires V).comparator d)=_
  rw [erase_wires_comparator]
  apply borrow_ext
  · intro j
    change (paddedIndex V j).val=(sourceMeta V).paddedIndex j.val
    change (if j.val<k V then j.val else
      BlockCircuit.bodyWires V+oldWork V+prepWork V+(j.val-k V)) =
      (if j.val<k V then j.val else BlockCircuit.bodyWires V+(oldWork V+prepWork V)+(j.val-k V))
    split_ifs <;> omega
  · intro j
    have hv : (![0,4,5] d : ℕ)=((![0,4,5] d : Fin 6)).val := by fin_cases d <;> rfl
    change (prepWord V (![0,4,5] d) j).val=(sourceMeta V).word (![0,4,5] d) j.val
    rw [hv]
    exact source_word V (![0,4,5] d) j
  · intro j; rfl
  · change BlockCircuit.bodyWires V+(oldWork V+6*r V)+(r V+1)=
      BlockCircuit.bodyWires V+(oldWork V+6*r V+(k V+3))
    dsimp only [r,k]
    omega
