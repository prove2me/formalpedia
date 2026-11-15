-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.select_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:59:57.479365+00:00
-- url     : https://prove2.me/submissions/b54f273c-d4e3-4b45-b77b-e7c131bbeeb7

/- Generated from Solutions.CertificateBlockCompilerCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
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
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_mid_transports
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_post_transports
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_verifier_transports

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

/- Inline helpers retained from Solutions.CircuitUnitary. -/
section


open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof



















theorem verifier_unitary {G : GateSet} (V : Verifier G) :
    V.unitary ∈ Matrix.unitaryGroup V.Wire ℂ := circuit_unitary V.gates





open scoped ComplexOrder



end QMAPerfectCompleteness.Main.CircuitProof

end

/- Inline helpers retained from Solutions.BlockEncoding. -/
section


/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)







































































/-- The verifier call called backwardGates in the compiler vocabulary is the exact adjoint. -/
theorem backwardGates_matrix (V : Verifier gatesG2) (w : ℕ) :
    circuitMatrix (BlockCircuit.backwardGates V w) =
      (circuitMatrix (BlockCircuit.forwardGates V w))ᴴ := by
  exact circuitMatrix_reverse_g2 _

end QMAPerfectCompleteness.Main.BlockProof

end

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

lemma mul_basisEmbedding {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (C : Matrix β β ℂ) (y : β) (x : α) : (C*basisEmbedding e) y x = C y (e x) := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,mul_ite]



lemma basisEmbedding_mul_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α → β) (f : α → α) (y : β) (x : α) :
    (basisEmbedding e * basisMap f) y x = if y = e (f x) then 1 else 0 := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,basisMap,ite_mul,mul_ite]

lemma transports_classical {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e f : α → β) (C : Matrix β β ℂ) (g : α → α)
    (hc : ∀ y x, C y (e x) = if y = f (g x) then 1 else 0) :
    Transports e f C (basisMap g) := by
  ext y x
  rw [mul_basisEmbedding,basisEmbedding_mul_classical]
  exact hc y x

variable (V : Verifier gatesG2)






































end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.BlockLogicalSelect. -/
section


/-! Abstract branch assembly for the literal block compiler. -/
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockLogicalSelect
variable (V : Verifier gatesG2)




lemma select_mul (F G : Fin (2^indexQubits V) → Matrix V.Body V.Body ℂ) :
    select V F * select V G = select V (fun j => F j * G j) := by
  classical
  ext y x
  rcases y with ⟨j,y⟩
  rcases x with ⟨k,x⟩
  by_cases h : j = k
  · subst j
    simp [select,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul]
  · simp [select,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul,h]



lemma select_const (M : Matrix V.Body V.Body ℂ) :
    select V (fun _ => M) = (1 : Matrix (Fin (2^indexQubits V)) _ ℂ) ⊗ₖ M := by
  classical
  ext y x
  simp [select,Matrix.kroneckerMap_apply,Matrix.one_apply,ite_mul]

lemma select_eq_sum (F : Fin (2^indexQubits V) → Matrix V.Body V.Body ℂ) :
    select V F = ∑ j, Matrix.single j j (1 : ℂ) ⊗ₖ F j := by
  classical
  ext y x
  by_cases h : y.1 = x.1
  · simp [select,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.single_apply,ite_and,
      ite_mul,mul_ite,eq_comm,h]
  · simp [select,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.single_apply,ite_and,
      ite_mul,mul_ite,eq_comm,h]





lemma onWires_mul (M N : Matrix V.Wire V.Wire ℂ) :
    V.onWires M * V.onWires N = V.onWires (M*N) := by
  simp only [Verifier.onWires,← Matrix.mul_kronecker_mul,Matrix.one_mul]

lemma onWires_one : V.onWires (1 : Matrix V.Wire V.Wire ℂ) = 1 := by
  simp only [Verifier.onWires,Matrix.one_kronecker_one]

lemma verifier_cancel : V.onWires V.unitaryᴴ * V.onWires V.unitary = 1 := by
  have hu : V.unitaryᴴ * V.unitary = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (CircuitProof.verifier_unitary V)
  rw [onWires_mul,hu,onWires_one]

lemma branch_assembly (z : V.Proof) (a b : ℕ) (j : Fin (2^indexQubits V)) :
    postBranch V z a b j * V.onWires V.unitaryᴴ * midBranch V a j * V.onWires V.unitary =
      V.branch z a b j.val := by
  by_cases ha : j.val < a
  · simp only [postBranch,midBranch,Verifier.branch,if_pos ha,Matrix.mul_one]
    rw [Matrix.mul_assoc,verifier_cancel,Matrix.mul_one]
  · by_cases hf : j.val < 3*a
    · simp only [postBranch,midBranch,Verifier.branch,if_neg ha,if_pos hf,Verifier.gadgetT,
        Matrix.neg_mul]
    · simp only [postBranch,midBranch,Verifier.branch,if_neg ha,if_neg hf,Matrix.mul_one]
      rw [Matrix.mul_assoc,verifier_cancel,Matrix.mul_one]

/-- The four physical SELECT stages produce exactly the branch matrix in the paper. -/
theorem select_assembly (z : V.Proof) (a b : ℕ) :
    select V (postBranch V z a b) *
      ((1 : Matrix (Fin (2^indexQubits V)) _ ℂ) ⊗ₖ V.onWires V.unitaryᴴ) *
      select V (midBranch V a) *
      ((1 : Matrix (Fin (2^indexQubits V)) _ ℂ) ⊗ₖ V.onWires V.unitary) =
      ∑ j : Fin (2^indexQubits V),Matrix.single j j (1 : ℂ) ⊗ₖ V.branch z a b j.val := by
  rw [← select_const,← select_const,select_mul,select_mul,select_mul,← select_eq_sum]
  congr 1
  funext j
  exact branch_assembly V z a b j

end QMAPerfectCompleteness.Main.BlockLogicalSelect

end

/- Inline helpers retained from Solutions.BlockTaggedActions. -/
section


/-! Deterministic block SELECT operations on the indexed predicate-tagged workspace fiber. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockStateCoordinates BlockClockCoordinates
variable (V : Verifier gatesG2)

















lemma midLogical_matrix (a b : ℕ) :
    basisMap (midLogical V a b) = BlockLogicalSelect.select V (BlockLogicalSelect.midBranch V a) := by
  ext y x
  by_cases ha : x.1.val < a
  · simp [basisMap,basisEmbedding,midLogical,Layout.rangeTruth,BlockLogicalSelect.select,
      BlockLogicalSelect.midBranch,ha,Matrix.one_apply,Prod.ext_iff,ite_and]
  · by_cases hf : x.1.val < 3*a
    · simp [basisMap,basisEmbedding,midLogical,Layout.rangeTruth,BlockLogicalSelect.select,
        BlockLogicalSelect.midBranch,ha,hf,Verifier.flipIf,Prod.ext_iff,ite_and]
    · simp [basisMap,basisEmbedding,midLogical,Layout.rangeTruth,BlockLogicalSelect.select,
        BlockLogicalSelect.midBranch,ha,hf,Matrix.one_apply,Prod.ext_iff,ite_and]











end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.BlockLogicalActions. -/
section


/-! Deterministic logical matrix entries for flag and clock operations. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements







lemma basisMap_mul {α : Type*} [Fintype α] (f g : α → α) :
    basisMap f * basisMap g = basisMap (f ∘ g) := by
  classical
  ext y x
  simp [basisMap,basisEmbedding,Matrix.mul_apply,Function.comp_apply,mul_ite]

variable (V : Verifier gatesG2)

lemma flipIf_basisMap (P : Clock V.proofQubits → V.Wire → Bool) :
    V.flipIf P = basisMap (fun x : V.Body => (x.1,x.2.1,xor x.2.2 (P x.1 x.2.1))) := by
  ext y x
  simp only [Verifier.flipIf,Matrix.of_apply,basisMap,basisEmbedding,Prod.ext_iff]

lemma shift_basisMap :
    V.shift = basisMap (fun x : V.Body => (x.1+1,x.2.1,x.2.2)) := by
  ext y x
  simp [Verifier.shift,basisMap,basisEmbedding,Matrix.kroneckerMap_apply,Matrix.one_apply,
    Prod.ext_iff,ite_and]
  split_ifs <;> rfl

lemma gadgetR_basisMap (z : V.Proof) :
    V.gadgetR z = basisMap (fun x : V.Body =>
      (x.1+1,x.2.1,xor x.2.2 (decide (x.1.val = ell V.proofQubits) && decide (V.proofPart x.2.1 = z)))) := by
  rw [Verifier.gadgetR,shift_basisMap,flipIf_basisMap,basisMap_mul]
  rfl

end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.BlockImplementation. -/
section


/-! Composition of the literal paper compiler on clean physical workspace. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates ReversibleGadgets BlockVerifierCoordinates BlockLogicalSelect
variable (V : Verifier gatesG2)













lemma postLogical_matrix (z : V.Proof) (a b : ℕ) :
    signedMap (postLogical V z a b)
        (fun p => if Layout.rangeTruth a b p.1.val 5 then (-1 : ℂ) else 1) =
      select V (postBranch V z a b) := by
  ext y x
  by_cases ha : x.1.val < a
  · have hf : x.1.val < 3*a := by omega
    have hu : x.1.val < 3*a+b := by omega
    simp [signedMap,postLogical,postFlagLogical,Layout.rangeTruth,select,postBranch,
      Verifier.flagX,flipIf_basisMap,basisMap,basisEmbedding,ha,hf,hu,Prod.ext_iff,ite_and]
  · by_cases hf : x.1.val < 3*a
    · have hu : x.1.val < 3*a+b := by omega
      simp [signedMap,postLogical,postFlagLogical,Layout.rangeTruth,select,postBranch,
        shift_basisMap,basisMap,basisEmbedding,ha,hf,hu,Prod.ext_iff,ite_and]
      simp only [neg_ite,neg_zero]
      rfl
    · by_cases hu : x.1.val < 3*a+b
      · simp [signedMap,postLogical,postFlagLogical,Layout.rangeTruth,select,postBranch,
          gadgetR_basisMap,basisMap,basisEmbedding,ha,hf,hu,Prod.ext_iff,ite_and]
        simp only [neg_ite,neg_zero]
        rfl
      · simp [signedMap,postLogical,postFlagLogical,Layout.rangeTruth,select,postBranch,
          basisMap,basisEmbedding,ha,hf,hu,Matrix.one_apply,Prod.ext_iff,ite_and]

end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.DynamicBlockCompiler. -/
section


/-! Dynamic range predicates for a coherent certificate, using three linear reversible comparators. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.DynamicBlockCompiler
open BlockCompiler BooleanCircuits ReversibleGadgets VariableComparison ComparisonCircuits



namespace RangeLayout
variable {n r : ℕ} (L : RangeLayout n r)




























theorem gates_matrix (y x : Basis n) (hx : L.Clean x) :
    circuitMatrix L.gates y x = if y = L.action x then 1 else 0 := L.program.sound y x hx

theorem action_clean (x : Basis n) (hx : L.Clean x) : L.Clean (L.action x) := L.program.preserves x hx



theorem action_tags (x : Basis n) (hx : ∀ i, x (L.tags i) = false) (i : Fin 6) :
    L.action x (L.tags i) = L.truth x i := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have h5 := hx 5
  fin_cases i <;>
    simp [action,program,CleanProgram.append,compareProgram,andNotProgram,compareAction,andNotAction,
      Function.comp_apply,L.bit_update_tag,L.tags.injective.eq_iff,h0,h1,h2,h3,h4,h5,truth]

theorem action_outside_tags (x : Basis n) (w : Fin n) (hw : ∀ i, w ≠ L.tags i) :
    L.action x w = x w := by
  simp [action,program,CleanProgram.append,compareProgram,andNotProgram,compareAction,andNotAction,
    Function.comp_apply,Function.update_of_ne,hw]









lemma undoProgram_gates : L.undoProgram.gates = L.gates.reverse := by
  simp only [gates,program,undoProgram,CleanProgram.append,CleanProgram.reverseOfInvolution,
    List.reverse_append,List.append_assoc]

theorem reverse_gates_matrix (y x : Basis n) (hx : L.Clean x) :
    circuitMatrix L.gates.reverse y x = if y = L.undoAction x then 1 else 0 := by
  rw [← L.undoProgram_gates]
  exact L.undoProgram.sound y x hx

@[simp] theorem undoAction_action (x : Basis n) : L.undoAction (L.action x) = x := by
  simp only [undoAction,action,undoProgram,program,CleanProgram.append,CleanProgram.reverseOfInvolution,
    compareProgram,andNotProgram,Function.comp_apply]
  rw [L.andNotAction_involutive 0 2 5 (by decide) (by decide),
    L.andNotAction_involutive 1 2 4 (by decide) (by decide),
    L.andNotAction_involutive 0 1 3 (by decide) (by decide),
    L.compareAction_involutive 2,L.compareAction_involutive 1,L.compareAction_involutive 0]









/-- A logical input encoding may be arbitrary, including coherent certificate registers. -/
theorem compute_transport {α : Type*} [Fintype α] [DecidableEq α]
    (e : α → Basis n) (he : ∀ p, L.Clean (e p)) :
    BlockImplements.Transports e (L.action ∘ e) (circuitMatrix L.gates) 1 := by
  have h := BlockImplements.transports_classical e (L.action ∘ e) (circuitMatrix L.gates) id
    (by intro y p; exact L.gates_matrix y (e p) (he p))
  have hid : BlockImplements.basisMap (id : α → α) = 1 := by
    ext y x
    simp [BlockImplements.basisMap,BlockImplements.basisEmbedding,Matrix.one_apply]
  rw [hid] at h
  exact h

theorem erase_transport {α : Type*} [Fintype α] [DecidableEq α]
    (e : α → Basis n) (he : ∀ p, L.Clean (e p)) :
    BlockImplements.Transports (L.action ∘ e) e (circuitMatrix L.gates.reverse) 1 := by
  have h := BlockImplements.transports_classical (L.action ∘ e) e (circuitMatrix L.gates.reverse) id
    (by
      intro y p
      rw [Function.comp_apply,L.reverse_gates_matrix _ _ (L.action_clean _ (he p)),L.undoAction_action]
      rfl)
  have hid : BlockImplements.basisMap (id : α → α) = 1 := by
    ext y x
    simp [BlockImplements.basisMap,BlockImplements.basisEmbedding,Matrix.one_apply]
  rw [hid] at h
  exact h

end RangeLayout
/-- Encoding-independent SELECT assembly for coherent certificate fibers. -/
theorem transports_chain {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    {e f : α → β} {R F M B P Q : Matrix β β ℂ} {U W X Y : Matrix α α ℂ}
    (hR : BlockImplements.Transports e f R 1) (hF : BlockImplements.Transports f f F U)
    (hM : BlockImplements.Transports f f M W) (hB : BlockImplements.Transports f f B X)
    (hP : BlockImplements.Transports f f P Y) (hQ : BlockImplements.Transports f e Q 1) :
    BlockImplements.Transports e e (Q*P*B*M*F*R) (Y*X*W*U) := by
  have h1 := BlockImplements.transports_mul e f f F R U 1 hF hR
  have h2 := BlockImplements.transports_mul e f f M (F*R) W (U*1) hM h1
  have h3 := BlockImplements.transports_mul e f f B (M*(F*R)) X (W*(U*1)) hB h2
  have h4 := BlockImplements.transports_mul e f f P (B*(M*(F*R))) Y (X*(W*(U*1))) hP h3
  have h5 := BlockImplements.transports_mul e f e Q (P*(B*(M*(F*R)))) 1 (Y*(X*(W*(U*1)))) hQ h4
  simpa only [Matrix.mul_assoc,Matrix.one_mul,Matrix.mul_one] using h5

end QMAPerfectCompleteness.Main.DynamicBlockCompiler

end

/- Inline helpers retained from Solutions.CertificateVerifierCoordinates. -/
section


/-! Lift the two quantum calls through retained certificate and workspace coordinates. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates BlockVerifierCoordinates ReversibleGadgets
























theorem forward_matrix (V : Verifier gatesG2) (w : ℕ) :
    circuitMatrix (forward V w) = physicalCall V w V.unitary := by
  rw [forward,circuitMatrix_mapWires,forwardGates,circuitMatrix_mapWires]
  rfl

theorem backward_matrix (V : Verifier gatesG2) (w : ℕ) :
    circuitMatrix (backward V w) = physicalCall V w V.unitaryᴴ := by
  rw [backward,circuitMatrix_mapWires,BlockProof.backwardGates_matrix,forwardGates,circuitMatrix_mapWires]
  simp only [physicalCall,placeMatrix,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rfl

end QMAPerfectCompleteness.Main.CertificateVerifierCoordinates

end

/- Inline helpers retained from Solutions.CertificateBlockCorrectness. -/
section


/-! Exact coherent block SELECT on the master certificate register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler
open ReversibleGadgets BlockImplements
variable (V : Verifier gatesG2)










@[simp] lemma coords_embed (s : Key V → Basis (work V)) (p : Logical V) :
    coords V (embed V s p) = (p,s (key V p)) := (coords V).apply_symm_apply _







lemma old_decode (x : Physical V) : BlockCircuit.decode (old V x) = (coords V x).1.1 := by
  rw [computationEquiv_body]
  rfl

@[simp] lemma embed_decode (s : Key V → Basis (work V)) (p : Logical V) :
    BlockCircuit.decode (old V (embed V s p)) = p.1 := by rw [old_decode,coords_embed]

lemma coords_work (x : Physical V) : (coords V x).2 = x ∘ workWire V := rfl

lemma embed_work (s : Key V → Basis (work V)) (p : Logical V) (i : Fin (work V)) :
    embed V s p (workWire V i) = s (key V p) i :=
  congrFun (congrArg Prod.snd (coords_embed V s p)) i



















lemma old_decode_eq (x y : Physical V)
    (h : ∀ w : Fin (total V), w.val < BlockCircuit.bodyWires V → x w = y w) :
    BlockCircuit.decode (old V x) = BlockCircuit.decode (old V y) := by
  apply Prod.ext
  · change Fin.ofNat _ (BlockCircuit.bitsValue (old V x) (layoutOf V).indexWire) = _
    congr 1
    unfold BlockCircuit.bitsValue
    apply Finset.sum_congr rfl
    intro i _
    rw [show old V x ((layoutOf V).indexWire i) = old V y ((layoutOf V).indexWire i) from
      h _ (by
        have hi : i.val < indexQubits V := i.isLt
        change i.val < BlockCircuit.bodyWires V
        dsimp only [BlockCircuit.bodyWires]
        omega)]
    rfl
  · apply Prod.ext
    · change Fin.ofNat _ (BlockCircuit.bitsValue (old V x) (layoutOf V).clockWire) = _
      congr 1
      unfold BlockCircuit.bitsValue
      apply Finset.sum_congr rfl
      intro i _
      rw [show old V x ((layoutOf V).clockWire i) = old V y ((layoutOf V).clockWire i) from
        h _ (by
          have hi : i.val < BlockCircuit.clockWires V := i.isLt
          change indexQubits V+i.val < BlockCircuit.bodyWires V
          dsimp only [BlockCircuit.bodyWires]
          omega)]
      rfl
    · apply Prod.ext
      · funext i
        exact h (oldEmbedding V ((layoutOf V).verifierWire i)) (by
          have := i.isLt
          change indexQubits V+BlockCircuit.clockWires V+i.val < BlockCircuit.bodyWires V
          dsimp only [BlockCircuit.bodyWires]; omega)
      · exact h (oldEmbedding V (layoutOf V).flagWire) (by
          change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) < BlockCircuit.bodyWires V
          simp only [BlockCircuit.bodyWires]; omega)

lemma range_body (x : Physical V) (w : Fin (total V)) (hw : w.val<BlockCircuit.bodyWires V) :
    (CertificateRangeCircuit.layout V).action x w = x w := by
  apply DynamicBlockCompiler.RangeLayout.action_outside_tags
  intro t h
  have ht := CertificateRangeCircuit.tag_bounds V t
  have hv := congrArg Fin.val h
  change w.val = (CertificateRangeCircuit.tags V t).val at hv
  omega

lemma range_claim (x : Physical V) (i : Fin (claimQubits V)) :
    (CertificateRangeCircuit.layout V).action x (Fin.natAdd (BlockCircuit.bodyWires V+work V) i) =
      x (Fin.natAdd (BlockCircuit.bodyWires V+work V) i) := by
  apply DynamicBlockCompiler.RangeLayout.action_outside_tags
  intro t h
  have ht := t.isLt
  have hw := work_ge_fifteen V
  have hv := congrArg Fin.val h
  change BlockCircuit.bodyWires V+work V+i.val = BlockCircuit.bodyWires V+t.val at hv
  omega





lemma prepared_tag_zero (s : Key V → Basis (work V)) (hs : Prepared V s)
    (p : Logical V) (i : Fin 6) : embed V s p (CertificateRangeCircuit.tags V i) = false := by
  exact hs.old_clean p ⟨i.val,by have := i.isLt; dsimp only [Layout.work]; omega⟩

/-- The actual three dynamic comparators produce the exact indexed tag workspace fiber. -/
lemma range_action_embed (s : Key V → Basis (work V)) (hs : Prepared V s) (p : Logical V) :
    (CertificateRangeCircuit.layout V).action (embed V s p) = embed V (taggedSpace V s) p := by
  apply (coords V).injective
  apply Prod.ext
  · apply Prod.ext
    · calc
        (coords V ((CertificateRangeCircuit.layout V).action (embed V s p))).1.1 =
            BlockCircuit.decode (old V ((CertificateRangeCircuit.layout V).action (embed V s p))) :=
          (old_decode V _).symm
        _ = BlockCircuit.decode (old V (embed V s p)) :=
          old_decode_eq V _ _ (range_body V (embed V s p))
        _ = p.1 := embed_decode V s p
        _ = (coords V (embed V (taggedSpace V s) p)).1.1 := by rw [coords_embed]
    · calc
        (coords V ((CertificateRangeCircuit.layout V).action (embed V s p))).1.2 =
            (coords V (embed V s p)).1.2 := by
          rw [computationEquiv_claim,computationEquiv_claim]
          congr 1
          funext i
          exact range_claim V (embed V s p) i
        _ = (coords V (embed V (taggedSpace V s) p)).1.2 := by rw [coords_embed,coords_embed]
  · rw [coords_work]
    funext i
    change (CertificateRangeCircuit.layout V).action (embed V s p) (workWire V i) =
      (coords V (embed V (taggedSpace V s) p)).2 i
    rw [coords_embed]
    by_cases hi : i.val<6
    · have he : workWire V i = CertificateRangeCircuit.tags V ⟨i.val,hi⟩ := by apply Fin.ext; rfl
      have ht := (CertificateRangeCircuit.layout V).action_tags (embed V s p)
        (prepared_tag_zero V s hs p) ⟨i.val,hi⟩
      have hv := congrFun (hs.range_truth p) ⟨i.val,hi⟩
      rw [he]
      exact ht.trans (hv.trans (dif_pos hi).symm)
    · have hout : ∀ t : Fin 6, workWire V i ≠ (CertificateRangeCircuit.layout V).tags t := by
        intro t h
        have hv := congrArg Fin.val h
        change BlockCircuit.bodyWires V+i.val = BlockCircuit.bodyWires V+t.val at hv
        have ht := t.isLt
        omega
      rw [(CertificateRangeCircuit.layout V).action_outside_tags (embed V s p) (workWire V i) hout,embed_work]
      simp only [taggedSpace,dif_neg hi]

lemma range_transports (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V s) (embed V (taggedSpace V s)) (circuitMatrix (CertificateRangeCircuit.gates V)) 1 := by
  have h := (CertificateRangeCircuit.layout V).compute_transport (embed V s) hs.range_clean
  have he : (CertificateRangeCircuit.layout V).action ∘ embed V s = embed V (taggedSpace V s) :=
    funext (range_action_embed V s hs)
  rw [he] at h
  exact h

lemma rangeUndo_transports (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V (taggedSpace V s)) (embed V s) (circuitMatrix (CertificateRangeCircuit.gates V).reverse) 1 := by
  have h := (CertificateRangeCircuit.layout V).erase_transport (embed V s) hs.range_clean
  have he : (CertificateRangeCircuit.layout V).action ∘ embed V s = embed V (taggedSpace V s) :=
    funext (range_action_embed V s hs)
  rw [he] at h
  exact h

end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

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






lemma basisMap_certificate (f : Claim V → V.BlockReg (indexQubits V) → V.BlockReg (indexQubits V)) :
    basisMap (fun p : Logical V => (f p.2 p.1,p.2)) = Matrix.blockDiagonal (fun c => basisMap (f c)) := by
  classical
  ext y x
  by_cases hc : y.2=x.2
  · simp [basisMap,basisEmbedding,Matrix.blockDiagonal_apply,Prod.ext_iff,hc]
  · simp [basisMap,basisEmbedding,Matrix.blockDiagonal_apply,Prod.ext_iff,hc]

lemma signedMap_certificate
    (f : Claim V → V.BlockReg (indexQubits V) → V.BlockReg (indexQubits V))
    (s : Claim V → V.BlockReg (indexQubits V) → ℂ) :
    signedMap (fun p : Logical V => (f p.2 p.1,p.2)) (fun p => s p.2 p.1) =
      Matrix.blockDiagonal (fun c => signedMap (f c) (s c)) := by
  classical
  ext y x
  by_cases hc : y.2=x.2
  · simp [signedMap,Matrix.blockDiagonal_apply,Prod.ext_iff,hc]
  · simp [signedMap,Matrix.blockDiagonal_apply,Prod.ext_iff,hc]

lemma middle_matrix : basisMap (middle V) = Matrix.blockDiagonal (fun c : Claim V =>
    select V (midBranch V c.2.1.val)) := by
  unfold middle
  rw [basisMap_certificate V (fun c : Claim V => BlockImplements.midLogical V c.2.1.val c.2.2.val)]
  congr 1
  funext c
  exact midLogical_matrix V c.2.1.val c.2.2.val

lemma post_matrix : signedMap (post V) (sign V) = Matrix.blockDiagonal (fun c : Claim V =>
    select V (postBranch V c.1 c.2.1.val c.2.2.val)) := by
  unfold post sign
  rw [signedMap_certificate V
    (fun c : Claim V => BlockImplements.postLogical V c.1 c.2.1.val c.2.2.val)
    (fun c p => if BlockCompiler.Layout.rangeTruth c.2.1.val c.2.2.val p.1.val 5 then (-1 : ℂ) else 1)]
  congr 1
  funext c
  exact postLogical_matrix V c.1 c.2.1.val c.2.2.val

lemma kronecker_identity_eq_blockDiagonal (M : Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ) :
    M ⊗ₖ (1 : Matrix (Claim V) (Claim V) ℂ) = Matrix.blockDiagonal (fun _ => M) := by
  classical
  ext y x
  simp [Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.blockDiagonal_apply,mul_ite]

lemma call_eq_blockDiagonal (M : Matrix V.Wire V.Wire ℂ) :
    CertificateVerifierCoordinates.logicalCall V M =
      Matrix.blockDiagonal (fun _ : Claim V => BlockVerifierCoordinates.logicalVerifier V M) :=
  kronecker_identity_eq_blockDiagonal V _

/-- Exact SELECT assembly, retaining all certificate coherences. -/
theorem select_assembly :
    signedMap (post V) (sign V) * CertificateVerifierCoordinates.logicalCall V V.unitaryᴴ *
      basisMap (middle V) * CertificateVerifierCoordinates.logicalCall V V.unitary =
      Matrix.blockDiagonal (fun c : Claim V =>
        ∑ j : Fin (2^indexQubits V),Matrix.single j j (1 : ℂ) ⊗ₖ V.branch c.1 c.2.1.val c.2.2.val j.val) := by
  rw [post_matrix,call_eq_blockDiagonal,middle_matrix,call_eq_blockDiagonal,
    ← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]
  congr 1
  funext c
  exact BlockLogicalSelect.select_assembly V c.1 c.2.1.val c.2.2.val



end QMAPerfectCompleteness.Main.CertificateLogicalSelect

end

/- Inline helpers retained from Solutions.CertificateQuantumTransports. -/
section


/-! Quantum calls and both H banks on the prepared arithmetic workspace fibers. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockImplements
variable (V : Verifier gatesG2)



lemma forward_transports (s : Key V → Basis (work V)) :
    Transports (embed V s) (embed V s)
      (circuitMatrix (CertificateVerifierCoordinates.forward V (work V)))
      (CertificateVerifierCoordinates.logicalCall V V.unitary) := by
  rw [CertificateVerifierCoordinates.forward_matrix]
  exact verifier_transports V s V.unitary

lemma backward_transports (s : Key V → Basis (work V)) :
    Transports (embed V s) (embed V s)
      (circuitMatrix (CertificateVerifierCoordinates.backward V (work V)))
      (CertificateVerifierCoordinates.logicalCall V V.unitaryᴴ) := by
  rw [CertificateVerifierCoordinates.backward_matrix]
  exact verifier_transports V s V.unitaryᴴ





end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

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



/-- The complete actual dynamic SELECT restores the prepared arithmetic workspace fiber. -/
theorem solution (s : Key V → Basis (work V)) (hs : Prepared V s) :
    Transports (embed V s) (embed V s) (circuitMatrix (selectGates V))
      (Matrix.blockDiagonal (fun c : CertificateMixture.Claim V =>
        ∑ j : Fin (2^indexQubits V),Matrix.single j j (1 : ℂ) ⊗ₖ V.branch c.1 c.2.1.val c.2.2.val j.val)) := by
  have hm := mid_transports V s hs
  have he : QMAPerfectCompleteness.Main.CertificateBlockCorrectness.midLogical V = CertificateLogicalSelect.middle V := rfl
  rw [he] at hm
  have h := DynamicBlockCompiler.transports_chain (range_transports V s hs)
    (forward_transports V (taggedSpace V s)) hm (backward_transports V (taggedSpace V s))
    (post_transports V s hs) (rangeUndo_transports V s hs)
  rw [CertificateLogicalSelect.select_assembly] at h
  simpa only [selectGates,BlockProof.circuitMatrix_append,Matrix.mul_assoc] using h
