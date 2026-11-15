-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificatePreparation.logical_eq_of_data
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:50:59.802622+00:00
-- url     : https://prove2.me/submissions/0159dd1d-ff4f-40f8-87ea-8a7ecf36aca7

/- Generated from Solutions.CertificateValidityPreparation by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

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
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits

/- Inline helpers retained from Solutions.BlockCoordinates. -/
section


/-! Exact basis coordinates for the published block register, including clean workspace. -/
open Matrix
namespace QMAPerfectCompleteness.Main.BlockCoordinates
open BlockCircuit IndexHadamards































theorem coordinates_fst (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) :
    (coordinates V w x).1 = decode x := by
  apply Prod.ext
  · apply Fin.ext
    change ComparisonCircuits.littleValue (x ∘ indexWire) =
      ComparisonCircuits.littleValue (x ∘ indexWire) % 2^indexQubits V
    exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow _)).symm
  · apply Prod.ext
    · apply Fin.ext
      change ComparisonCircuits.littleValue (x ∘ clockWire) =
        bitsValue x clockWire % (ell V.proofQubits+1)
      rw [clock_card]
      exact (Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow (x ∘ clockWire))).symm
    · rfl



















end QMAPerfectCompleteness.Main.BlockCoordinates

end

/- Inline helpers retained from Solutions.CertificateCoordinates. -/
section


/-! Concrete qubit coordinates for a coherent binary certificate and its history proof. -/
namespace QMAPerfectCompleteness.Main.CertificateCoordinates
open BlockCircuit BlockCoordinates IndexHadamards CertificateMixture














@[simp] theorem computationEquiv_body (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.1 = decode (fun i => x (Fin.castAdd (claimQubits V) i)) :=
  coordinates_fst V w _

@[simp] theorem computationEquiv_claim (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).1.2 = claimEquiv V (fun i => x (Fin.natAdd (bodyWires V+w) i)) := rfl



end QMAPerfectCompleteness.Main.CertificateCoordinates

end



/-! The actual arithmetic-plus-validity prefix and its certificate-dependent workspace fiber. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
end QMAPerfectCompleteness.Main.CertificatePreparation
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits CertificateValidityCircuit
variable (V : Verifier gatesG2)

theorem solution (x y : Physical V)
    (hdata : ∀ w : Fin (total V), w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val → x w=y w) :
    (coords V x).1=(coords V y).1 := by
  apply Prod.ext
  · rw [computationEquiv_body,computationEquiv_body]
    change decode (fun i => x (Fin.castAdd (claimQubits V) i)) =
      decode (fun i => y (Fin.castAdd (claimQubits V) i))
    apply Prod.ext
    · change Fin.ofNat (2^indexQubits V)
        (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) indexWire) =
        Fin.ofNat (2^indexQubits V) (bitsValue (fun i => y (Fin.castAdd (claimQubits V) i)) indexWire)
      congr 1
      unfold bitsValue
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply congrArg (fun b : Bool => b=true)
      apply hdata
      left
      have hi := i.isLt
      change i.val < bodyWires V
      dsimp [bodyWires]
      omega
    · apply Prod.ext
      · change Fin.ofNat (ell V.proofQubits+1)
          (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) clockWire) =
          Fin.ofNat (ell V.proofQubits+1) (bitsValue (fun i => y (Fin.castAdd (claimQubits V) i)) clockWire)
        congr 1
        unfold bitsValue
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply congrArg (fun b : Bool => b=true)
        apply hdata
        left
        have hi := i.isLt
        change indexQubits V+i.val < bodyWires V
        dsimp [bodyWires]
        omega
      · apply Prod.ext
        · funext i
          apply hdata
          left
          have hi := i.isLt
          change indexQubits V+clockWires V+i.val < bodyWires V
          dsimp [bodyWires]
          omega
        · apply hdata
          left
          change indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) < bodyWires V
          dsimp [bodyWires]
          omega
  · rw [computationEquiv_claim,computationEquiv_claim]
    congr 1
    funext i
    apply hdata
    right
    change bodyWires V+work V ≤ bodyWires V+work V+i.val
    omega
