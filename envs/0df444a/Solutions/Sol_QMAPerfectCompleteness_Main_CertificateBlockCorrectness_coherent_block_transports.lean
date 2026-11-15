-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.coherent_block_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:08:51.188888+00:00
-- url     : https://prove2.me/submissions/a7d31615-a45d-479b-b16b-6c165576ee1d

/- Generated from Solutions.CertificateBlockCompilerCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_hadamard_transports
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_select_transports

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

/- Inline helpers retained from Solutions.BlockImplements. -/
section


/-! Exact realization of the literal paper compiler on the published wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockClockCoordinates ReversibleGadgets





theorem transports_mul {α β : Type*} [Fintype α] [Fintype β]
    (e f g : α → β) (C D : Matrix β β ℂ) (U W : Matrix α α ℂ)
    (hC : Transports f g C U) (hD : Transports e f D W) :
    Transports e g (C*D) (U*W) := by
  unfold Transports at *
  rw [Matrix.mul_assoc,hD,← Matrix.mul_assoc,hC,Matrix.mul_assoc]









variable (V : Verifier gatesG2)






































end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.CertificateLogicalSelect. -/
section


/-! Certificate-diagonal logical assembly of the coherent block SELECT. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateLogicalSelect
open BlockImplements BlockLogicalSelect CertificateMixture
variable (V : Verifier gatesG2)














lemma kronecker_identity_eq_blockDiagonal (M : Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ) :
    M ⊗ₖ (1 : Matrix (Claim V) (Claim V) ℂ) = Matrix.blockDiagonal (fun _ => M) := by
  classical
  ext y x
  simp [Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.blockDiagonal_apply,mul_ite]





/-- The same literal H banks give the paper block unitary on each certificate branch. -/
theorem full_assembly :
    CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V)) *
      Matrix.blockDiagonal (fun c : Claim V =>
        ∑ j : Fin (2^indexQubits V),Matrix.single j j (1 : ℂ) ⊗ₖ V.branch c.1 c.2.1.val c.2.2.val j.val) *
      CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V)) =
      Matrix.blockDiagonal (fun c : Claim V => V.blockUnitary (indexQubits V) c.1 c.2.1.val c.2.2.val) := by
  have hH : CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V)) =
      Matrix.blockDiagonal (fun _ : Claim V => indexHadamard (indexQubits V) ⊗ₖ (1 : Matrix V.Body V.Body ℂ)) :=
    kronecker_identity_eq_blockDiagonal V _
  simp only [hH,← Matrix.blockDiagonal_mul]
  rfl

end QMAPerfectCompleteness.Main.CertificateLogicalSelect

end



/-! Exact coherent master-layout block circuit, with literal dynamic comparisons. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockCompiler BlockImplements
variable (V : Verifier gatesG2)







/-- Literal coherent block correctness on any prepared certificate-dependent workspace.
All certificate coherences are retained and all dynamic branch tags are erased. -/
theorem solution (s : CertificateMixture.Claim V → Basis (work V))
    (hs : Prepared V (certSpace V s)) :
    Transports (embed V (certSpace V s)) (embed V (certSpace V s)) (circuitMatrix (gates V))
      (Matrix.blockDiagonal (fun c : CertificateMixture.Claim V =>
        V.blockUnitary (indexQubits V) c.1 c.2.1.val c.2.2.val)) := by
  let e := embed V (certSpace V s)
  have hH := hadamard_transports V s
  have hS := select_transports V (certSpace V s) hs
  have hSH := transports_mul e e e _ _ _ _ hS hH
  have hHSH := transports_mul e e e _ _ _ _ hH hSH
  have h : Transports e e (circuitMatrix (gates V))
      (CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V)) *
        Matrix.blockDiagonal (fun c : CertificateMixture.Claim V =>
          ∑ j : Fin (2^indexQubits V),Matrix.single j j (1 : ℂ) ⊗ₖ V.branch c.1 c.2.1.val c.2.2.val j.val) *
        CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V))) := by
    simpa only [gates,BlockProof.circuitMatrix_append,Matrix.mul_assoc] using hHSH
  rw [CertificateLogicalSelect.full_assembly] at h
  exact h
