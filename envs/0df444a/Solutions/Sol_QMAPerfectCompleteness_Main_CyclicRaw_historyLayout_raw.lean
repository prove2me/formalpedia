-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicRaw.historyLayout_raw
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:52:20.757133+00:00
-- url     : https://prove2.me/submissions/5596aa81-5381-49e7-b5fe-937a708bf4c2

/- Generated from Solutions.CyclicRawCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
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
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect



/-! Literal raw-code correspondence for the coherent certificate compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace QMAPerfectCompleteness.Main.CyclicRaw
end QMAPerfectCompleteness.Main.CyclicRaw
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding RawG2 CertificateMasterLayout






@[ext] theorem QMAPerfectCompleteness.Main.CyclicRaw.borrow_ext {r : ℕ} (L M : RawG2.BorrowLayout r)
    (ha : ∀j,L.left j=M.left j) (hb : ∀j,L.right j=M.right j)
    (hc : ∀j,L.carry j=M.carry j) (hp : L.temp=M.temp) : L=M := by
  cases L; cases M
  simp only [BorrowLayout.mk.injEq]
  exact ⟨funext ha,funext hb,funext hc,hp⟩




















@[simp] theorem solution (V : Verifier gatesG2) :
    eraseHistory (CertificateMasterLayout.historyLayout V)=(sourceMeta V).historyLayout := by
  change HistoryLayout.mk _ _ _ = HistoryLayout.mk _ _ _
  congr 1
  · apply borrow_ext
    · intro j
      change (if j.val<V.proofQubits then indexQubits V+BlockCircuit.clockWires V+j.val else _)=_
      rw [if_pos j.isLt]
      rfl
    · intro j
      change (if V.proofQubits+j.val<V.proofQubits then _ else
        if V.proofQubits+j.val<2*V.proofQubits then _ else _)=_
      rw [if_neg (by omega),if_pos (by have := j.isLt; omega)]
      change BlockCircuit.bodyWires V+work V+(V.proofQubits+j.val-V.proofQubits)=_
      change BlockCircuit.bodyWires V+work V+(V.proofQubits+j.val-V.proofQubits)=
        BlockCircuit.bodyWires V+work V+j.val
      omega
    · intro j
      change (if 2*V.proofQubits+j.val<V.proofQubits then _ else
        if 2*V.proofQubits+j.val<2*V.proofQubits then _ else
        if 2*V.proofQubits+j.val<3*V.proofQubits+1 then _ else _)=_
      rw [if_neg (by omega),if_neg (by omega),if_pos (by have := j.isLt; omega)]
      change BlockCircuit.bodyWires V+11+(2*V.proofQubits+j.val-2*V.proofQubits)=_
      change BlockCircuit.bodyWires V+11+(2*V.proofQubits+j.val-2*V.proofQubits)=
        BlockCircuit.bodyWires V+(11+j.val)
      omega
    · change (if 3*V.proofQubits+1<V.proofQubits then _ else
        if 3*V.proofQubits+1<2*V.proofQubits then _ else
        if 3*V.proofQubits+1<3*V.proofQubits+1 then _ else _)=_
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      rfl
  · funext j
    fin_cases j <;> rfl
