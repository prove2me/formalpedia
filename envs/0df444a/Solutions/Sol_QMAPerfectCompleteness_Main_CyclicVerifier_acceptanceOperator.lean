-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CyclicVerifier.acceptanceOperator
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T17:20:04.594177+00:00
-- url     : https://prove2.me/submissions/9636ae67-b64c-4815-93f7-4f083ad11448

/- Generated from Solutions.CyclicVerifier by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
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
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificateBlockCorrectness_actual_coherent_block_transports
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificatePreparation_logical_eq_of_data
import Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_values

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
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect

/- Inline helpers retained from Solutions.BlockEncoding. -/
section


/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)

@[simp] theorem proofPart_initialState (p : V.Proof) : V.proofPart (V.initialState p) = p := by
  funext i
  simp [Verifier.proofPart, Verifier.initialState]

theorem initialState_injective : Function.Injective V.initialState := by
  intro p q hpq
  have := congrArg V.proofPart hpq
  simpa using this















/-- The zEmbed matrix selects one basis state for each history basis vector. -/
theorem zEmbed_apply (k : ℕ) (f : Bool) (y : V.BlockReg k) (x : History V) :
    V.zEmbed k f y x = if y = (0, bodyInitial V f x) then 1 else 0 := by
  simp only [Verifier.zEmbed, Matrix.of_apply, bodyInitial, Prod.ext_iff]

/-- Taking the designated input and output ancilla block is simply entry selection. -/
theorem zEmbed_sandwich (k : ℕ) (f g : Bool)
    (M : Matrix (V.BlockReg k) (V.BlockReg k) ℂ) (y x : History V) :
    ((V.zEmbed k f)ᴴ * M * V.zEmbed k g) y x =
      M (0, bodyInitial V f y) (0, bodyInitial V g x) := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, zEmbed_apply]



















































end QMAPerfectCompleteness.Main.BlockProof

end

/- Inline helpers retained from Solutions.BooleanFraming. -/
section


/-! Inverses and frame rules for the concrete Boolean straight-line compiler. -/
namespace QMAPerfectCompleteness.Main.BooleanCircuits





lemma evalCommand_outside {n : ℕ} (c : Command n) (x : Basis n) (w : Fin n)
    (hw : w ≠ c.target) : evalCommand c x w = x w := by
  cases c <;> exact Function.update_of_ne hw _ _

lemma eval_outside {n : ℕ} (p : List (Command n)) (x : Basis n) (w : Fin n)
    (hw : ∀ c ∈ p, w ≠ c.target) : eval p x w = x w := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih =>
    change eval p (evalCommand c x) w = _
    rw [ih _ (fun d hd => hw d (List.mem_cons_of_mem c hd)),
      evalCommand_outside c x w (hw c (List.mem_cons_self))]

lemma evalCommand_involutive {n : ℕ} (c : Command n) : Function.Involutive (evalCommand c) := by
  intro x
  funext w
  cases c with
  | flip t =>
    by_cases h : w=t
    · subst w; simp [evalCommand]
    · simp [evalCommand,Function.update_of_ne h]
  | copy a t hat =>
    by_cases h : w=t
    · subst w; simp [evalCommand,Function.update_of_ne hat]
    · simp [evalCommand,Function.update_of_ne h]
  | conj a b t hat hbt =>
    by_cases h : w=t
    · subst w; simp [evalCommand,Function.update_of_ne hat,Function.update_of_ne hbt]
    · simp [evalCommand,Function.update_of_ne h]

lemma eval_append' {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih => exact ih _

/-- Reversal uncomputes the exact classical state, rather than only a measured observable. -/
theorem eval_reverse_left {n : ℕ} (p : List (Command n)) (x : Basis n) :
    eval p.reverse (eval p x) = x := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih =>
    rw [List.reverse_cons,eval_append']
    change evalCommand c (eval p.reverse (eval p (evalCommand c x))) = x
    rw [ih,evalCommand_involutive]



lemma evalCommand_agrees {n : ℕ} (S : Set (Fin n)) (c : Command n) (hc : c.Within S)
    (x y : Basis n) (h : ∀ w ∈ S, x w = y w) :
    ∀ w ∈ S, evalCommand c x w = evalCommand c y w := by
  intro w hw
  cases c with
  | flip t =>
    by_cases ht : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t hc]
    · simpa only [evalCommand,Function.update_of_ne ht] using h w hw
  | copy a t hat =>
    obtain ⟨ha,ht⟩ := hc
    by_cases hwt : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t ht,h a ha]
    · simpa only [evalCommand,Function.update_of_ne hwt] using h w hw
  | conj a b t hat hbt =>
    obtain ⟨ha,hb,ht⟩ := hc
    by_cases hwt : w=t
    · subst w; simp only [evalCommand,Function.update_self]; rw [h t ht,h a ha,h b hb]
    · simpa only [evalCommand,Function.update_of_ne hwt] using h w hw

/-- A program reads only its declared frame. Unrelated output wires may change between the
forward compute phase and its reverse, while all scratch is still correctly uncomputed. -/
theorem eval_agrees {n : ℕ} (S : Set (Fin n)) (p : List (Command n))
    (hp : ∀ c ∈ p, c.Within S) (x y : Basis n) (h : ∀ w ∈ S, x w = y w) :
    ∀ w ∈ S, eval p x w = eval p y w := by
  induction p generalizing x y with
  | nil => exact h
  | cons c p ih =>
    exact ih (fun d hd => hp d (List.mem_cons_of_mem c hd)) _ _
      (evalCommand_agrees S c (hp c List.mem_cons_self) x y h)

end QMAPerfectCompleteness.Main.BooleanCircuits

end

/- Inline helpers retained from Solutions.VariableAddition. -/
section


/-! Literal variable-register addition using a ripple carry, copied sums, and uncomputation. -/
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.VariableAddition
open BooleanCircuits ComparisonCircuits ClockCircuits











lemma eval_append {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih => exact ih _



namespace Layout
variable {r n : ℕ} (L : Layout r n)



















@[simp] lemma step_zero (j : Fin r) : L.step j 0 = L.left j := rfl
@[simp] lemma step_one (j : Fin r) : L.step j 1 = L.right j := rfl
@[simp] lemma step_two (j : Fin r) : L.step j 2 = L.carry j.castSucc := rfl
@[simp] lemma step_three (j : Fin r) : L.step j 3 = L.carry j.succ := rfl
@[simp] lemma step_four (j : Fin r) : L.step j 4 = L.temp := rfl



































lemma temp_ne_output (j : Fin r) : L.temp ≠ L.output j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hj := j.isLt
  change 4*r+1 = 3*r+1+j.val at hv
  omega















/-- Every command in the output-copy phase changes exactly an output wire. -/
lemma sumCommands_target (js : List (Fin r)) (c : Command n) (hc : c ∈ L.sumCommands js) :
    ∃ j ∈ js, c.target = L.output j := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  refine ⟨j,hj,?_⟩
  simp only [sumStep,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h|h|h <;> subst c <;> rfl



lemma carryCommands_within (j : Fin r) :
    ∀ c ∈ carryCommands (L.step j), c.Within L.inputFrame := by
  simp [carryCommands,Command.Within,step_zero,step_one,step_two,step_three,step_four,
    inputFrame,L.left_ne_output,L.right_ne_output,L.temp_ne_output,
    fun i k => (L.output_ne_carry k i).symm]

lemma carryPrefix_within (t : ℕ) (ht : t ≤ r) :
    ∀ c ∈ L.carryPrefix t ht, c.Within L.inputFrame := by
  induction t with
  | zero => simp [carryPrefix]
  | succ t ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact ih (by omega) c hc
    · exact L.carryCommands_within _ c hc

lemma sumCommands_frame (js : List (Fin r)) (x : Basis n) (w : Fin n) (hw : w ∈ L.inputFrame) :
    eval (L.sumCommands js) x w = x w := by
  apply BooleanCircuits.eval_outside
  intro c hc
  obtain ⟨j,_,ht⟩ := L.sumCommands_target js c hc
  rw [ht]
  exact hw j









/-- Addition restores every nonoutput wire, including both inputs, carry chain, and temporary. -/
theorem commands_frame (x : Basis n) (w : Fin n) (hw : w ∈ L.inputFrame) :
    eval L.commands x w = x w := by
  let p := L.carryPrefix r le_rfl
  let q := L.sumCommands (List.finRange r)
  have hp : ∀ c ∈ p.reverse, c.Within L.inputFrame := by
    intro c hc
    exact L.carryPrefix_within r le_rfl c (List.mem_reverse.mp hc)
  have hag := BooleanCircuits.eval_agrees L.inputFrame p.reverse hp
    (eval q (eval p x)) (eval p x)
    (fun v hv => L.sumCommands_frame _ _ v hv)
  change eval (p++q++p.reverse) x w = x w
  rw [eval_append,eval_append]
  rw [hag w hw,eval_reverse_left]











end Layout
end QMAPerfectCompleteness.Main.VariableAddition

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

/- Inline helpers retained from Solutions.CoherentCertificate. -/
section


/-! Coherent certificate control, invalid-claim rejection, and the final acceptance bridge.
This module proves the measurement algebra independently of how the literal dynamic
comparison circuit is synthesized. -/
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture VerifierAnalysis










lemma zEmbed_isometry (V : Verifier gatesG2) (k : ℕ) (f : Bool) :
    (V.zEmbed k f)ᴴ * V.zEmbed k f = 1 := by
  ext y x
  have h := BlockProof.zEmbed_sandwich V k f f 1 y x
  simpa [Matrix.one_mul,Matrix.one_apply,BlockProof.bodyInitial,Prod.ext_iff,
    (BlockProof.initialState_injective V).eq_iff] using h



/-- Invalid claims need not control or skip the block circuit. Any unitary behaviour on an
invalid branch is compatible with unconditional rejection. This avoids a global validity
control on every quantum gate. -/
theorem rejection_effect_of_unitary_branches (V : Verifier gatesG2)
    (U : Claim V → Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ)
    (hvalid : ∀ c, IsValidCertificate V c.2.1 c.2.2 →
      U c = V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2)
    (hunitary : ∀ c, ¬IsValidCertificate V c.2.1 c.2.2 → (U c)ᴴ * U c = 1) :
    (initialIsometry V)ᴴ * (Matrix.blockDiagonal U)ᴴ * rejectProjector V *
      Matrix.blockDiagonal U * initialIsometry V = Matrix.blockDiagonal (claimRejection V) := by
  classical
  simp only [initialIsometry,rejectProjector,Matrix.blockDiagonal_conjTranspose,
    ← Matrix.blockDiagonal_mul]
  congr 1
  funext c
  by_cases hv : IsValidCertificate V c.2.1 c.2.2
  · rw [hvalid c hv]
    simp only [if_pos hv,claimRejection,ProofSetup.rejectionBlock,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  · simp only [if_neg hv,Matrix.mul_one,claimRejection]
    rw [Matrix.mul_assoc _ _ (U c),hunitary c hv,Matrix.mul_one,zEmbed_isometry]









end QMAPerfectCompleteness.Main.CoherentCertificate

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

@[simp] theorem computationEquiv_work (V : Verifier gatesG2) (w : ℕ)
    (x : Basis ((bodyWires V+w)+claimQubits V)) :
    (computationEquiv V w x).2 =
      fun i => x (Fin.castAdd (claimQubits V) (workspaceWire i)) := rfl

end QMAPerfectCompleteness.Main.CertificateCoordinates

end

/- Inline helpers retained from Solutions.CertificateVerifierLayout. -/
section


/-! Reordering the actual coherent-certificate wires into the published verifier convention:
history and certificate first, followed by index, verifier ancillas, flag and workspace. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierLayout
open CertificateCoordinates BlockCircuit ReversibleGadgets











lemma place_equiv_matrix {r n : ℕ} (e : Fin r ≃ Fin n) (A : Matrix (Basis r) (Basis r) ℂ) :
    placeMatrix e.toEmbedding A = A.submatrix (fun x => x ∘ e) (fun x => x ∘ e) := by
  ext y x
  rw [placeMatrix_apply]
  have hm : ∀ w, (∀ a, e a ≠ w) → y w = x w := by
    intro w h
    exact False.elim (h (e.symm w) (e.apply_symm_apply w))
  exact if_pos hm

theorem verifier_unitary (V : Verifier gatesG2) (w : ℕ)
    (gs : List (Instr gatesG2 ((bodyWires V+w)+claimQubits V)))
    (output : Fin ((bodyWires V+w)+claimQubits V)) :
    (verifier V w gs output).unitary =
      (circuitMatrix gs).submatrix (basisEquiv V w) (basisEquiv V w) := by
  change circuitMatrix (gs.map (Instr.mapWires (wireEquiv V w).toEmbedding)) = _
  rw [circuitMatrix_mapWires,place_equiv_matrix]
  rfl








lemma wireEquiv_index (V : Verifier gatesG2) (w : ℕ) (i : Fin (indexQubits V)) :
    wireEquiv V w (physicalIndex V w i) = Fin.natAdd (proofQubits V)
      (Fin.castAdd (V.ancillaQubits+1+w) i) := by
  apply Fin.ext
  have hi := i.isLt
  dsimp [wireEquiv,reorder,physicalIndex]
  split_ifs <;> (try dsimp [proofQubits,bodyWires,ancillaQubits] at *) <;> omega

lemma wireEquiv_history (V : Verifier gatesG2) (w : ℕ) (i : Fin (clockWires V+V.proofQubits)) :
    wireEquiv V w (physicalHistory V w i) = Fin.castAdd (ancillaQubits V w)
      (Fin.castAdd (claimQubits V) i) := by
  apply Fin.ext
  have hi := i.isLt
  dsimp [wireEquiv,reorder,physicalHistory]
  split_ifs <;> (try dsimp [proofQubits,bodyWires,ancillaQubits] at *) <;> omega

lemma wireEquiv_ancilla (V : Verifier gatesG2) (w : ℕ) (i : Fin (V.ancillaQubits+1+w)) :
    wireEquiv V w (physicalAncilla V w i) = Fin.natAdd (proofQubits V)
      (Fin.natAdd (indexQubits V) i) := by
  apply Fin.ext
  have hi := i.isLt
  dsimp [wireEquiv,reorder,physicalAncilla]
  split_ifs <;> (try dsimp [proofQubits,bodyWires,ancillaQubits] at *) <;> omega

lemma wireEquiv_claim (V : Verifier gatesG2) (w : ℕ) (i : Fin (claimQubits V)) :
    wireEquiv V w (physicalClaim V w i) = Fin.castAdd (ancillaQubits V w)
      (Fin.natAdd (clockWires V+V.proofQubits) i) := by
  apply Fin.ext
  have hi := i.isLt
  dsimp [wireEquiv,reorder,physicalClaim]
  split_ifs <;> (try dsimp [proofQubits,bodyWires,ancillaQubits] at *) <;> omega



@[simp] theorem prepared_index (V : Verifier gatesG2) (w : ℕ) (p : Basis (proofQubits V))
    (i : Fin (indexQubits V)) : prepared V w p (physicalIndex V w i) = false := by
  change (Fin.append p (fun _ : Fin (ancillaQubits V w) => false)) (wireEquiv V w (physicalIndex V w i)) = _
  rw [wireEquiv_index,Fin.append_right]
@[simp] theorem prepared_history (V : Verifier gatesG2) (w : ℕ) (p : Basis (proofQubits V))
    (i : Fin (clockWires V+V.proofQubits)) :
    prepared V w p (physicalHistory V w i) = p (Fin.castAdd (claimQubits V) i) := by
  change (Fin.append p (fun _ : Fin (ancillaQubits V w) => false)) (wireEquiv V w (physicalHistory V w i)) = _
  rw [wireEquiv_history,Fin.append_left]
@[simp] theorem prepared_ancilla (V : Verifier gatesG2) (w : ℕ) (p : Basis (proofQubits V))
    (i : Fin (V.ancillaQubits+1+w)) : prepared V w p (physicalAncilla V w i) = false := by
  change (Fin.append p (fun _ : Fin (ancillaQubits V w) => false)) (wireEquiv V w (physicalAncilla V w i)) = _
  rw [wireEquiv_ancilla,Fin.append_right]
@[simp] theorem prepared_claim (V : Verifier gatesG2) (w : ℕ) (p : Basis (proofQubits V))
    (i : Fin (claimQubits V)) : prepared V w p (physicalClaim V w i) =
      p (Fin.natAdd (clockWires V+V.proofQubits) i) := by
  change (Fin.append p (fun _ : Fin (ancillaQubits V w) => false)) (wireEquiv V w (physicalClaim V w i)) = _
  rw [wireEquiv_claim,Fin.append_left]

end QMAPerfectCompleteness.Main.CertificateVerifierLayout

end

/- Inline helpers retained from Solutions.CertificateReadout. -/
section


/-! A literal final acceptance flag for the coherent certificate verifier: valid AND Z≠0.
The zero-test work bit and every shared scratch flag are restored. -/
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateReadout
open ReversibleGadgets ControlCircuits EqualityCircuits BooleanCircuits BlockCompiler



namespace Layout
variable {r n : ℕ} (L : Layout r n)





























lemma program_action (x : Basis n) :
    L.program.action x = Function.update x L.output
      (xor (x L.output) (x L.valid && !(xor (x L.zero) (decide (L.allZero x))))) := by
  funext w
  by_cases hz : w=L.zero
  · subst w
    simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,zeroProgram,flagProgram,
      zeroAction,flagAction,L.allZero_update,Function.update_apply,L.tags.injective.eq_iff]
  · by_cases ho : w=L.output
    · subst w
      simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,zeroProgram,flagProgram,
        zeroAction,flagAction,L.allZero_update,Function.update_apply,L.tags.injective.eq_iff]
    · simp [program,CleanProgram.append,CleanProgram.reverseOfInvolution,zeroProgram,flagProgram,
        zeroAction,flagAction,L.allZero_update,Function.update_apply,hz,ho]

/-- Valid claims accept exactly when Z is not all zero; invalid claims never accept.
Every source wire and all readout workspace except the acceptance output are preserved. -/
theorem gates_matrix (y x : Basis n) (hx : L.Clean x) (hz : x L.zero = false) :
    circuitMatrix L.gates y x = if y = Function.update x L.output
      (xor (x L.output) (x L.valid && !(decide (L.allZero x)))) then 1 else 0 := by
  rw [gates,L.program.sound y x hx,L.program_action]
  simp [hz]



end Layout
end QMAPerfectCompleteness.Main.CertificateReadout

end

/- Inline helpers retained from Solutions.CertificateMasterReadout. -/
section


/-! Instantiation of the final physical acceptance flag on the coherent verifier layout. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open BlockCircuit CertificateReadout
variable (V : Verifier gatesG2)





















@[simp] theorem readout_valid : (readoutLayout V).valid = validity V 5 := by
  apply Fin.ext
  change bodyWires V+(oldWork V+prepWork V+7) = bodyWires V+(oldWork V+prepWork V+2)+5
  omega
@[simp] theorem readout_zero : (readoutLayout V).zero = readoutTags V 0 := by
  apply Fin.ext
  change bodyWires V+(oldWork V+prepWork V+8+readoutWork V) =
    bodyWires V+(oldWork V+prepWork V+2+6+readoutWork V)+0
  omega
@[simp] theorem readout_output : (readoutLayout V).output = readoutTags V 1 := by
  apply Fin.ext
  change bodyWires V+(oldWork V+prepWork V+9+readoutWork V) =
    bodyWires V+(oldWork V+prepWork V+2+6+readoutWork V)+1
  omega

end QMAPerfectCompleteness.Main.CertificateMasterLayout

end

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

/- Inline helpers retained from Solutions.CertificateValidity. -/
section


/-! Exact polynomial-size certificate validity predicates for the coherent verifier. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateValidity
open BlockCompiler ReversibleGadgets ControlCircuits ComparisonCircuits VariableComparison





lemma checks_iff (k a b : ℕ) (hk : 3 ≤ k) :
    (∀ i, checks k a b i = true) ↔
      0<a ∧ 0<b ∧ 2^k≤8*a ∧ 4*a≤2^k ∧ 2*b≤a := by
  have h3 : 2^k = 8*2^(k-3) := by
    calc
      2^k = 2^((k-3)+3) := by rw [Nat.sub_add_cancel hk]
      _ = 8*2^(k-3) := by rw [pow_add]; norm_num; omega
  have h2 : 2^k = 4*2^(k-2) := by
    calc
      2^k = 2^((k-2)+2) := by rw [Nat.sub_add_cancel (by omega : 2≤k)]
      _ = 4*2^(k-2) := by rw [pow_add]; norm_num; omega
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2' := h 2
    have h3' := h 3
    have h4 := h 4
    simp [checks] at h0 h1 h2' h3' h4
    omega
  · rintro ⟨ha,hb,hl,hu,hb2⟩ i
    fin_cases i <;> simp [checks] <;> omega

lemma checks_iff_valid (V : Verifier gatesG2) (a b : ℕ) (hk : 3 ≤ indexQubits V)
    (ha : a < 2^indexQubits V) (hb : b < 2^indexQubits V) :
    (∀ i, checks (indexQubits V) a b i = true) ↔ IsValidCertificate V a b := by
  rw [checks_iff _ _ _ hk]
  unfold IsValidCertificate
  omega



namespace Layout
variable {k n : ℕ} (L : Layout k n)








lemma aValue_update (x : Basis n) (t : Fin 5) (v : Bool) :
    L.aValue (Function.update x (L.tags t) v) = L.aValue x := by
  unfold aValue BlockCircuit.bitsValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.update_of_ne (L.tag_a t i).symm]

lemma bValue_update (x : Basis n) (t : Fin 5) (v : Bool) :
    L.bValue (Function.update x (L.tags t) v) = L.bValue x := by
  unfold bValue BlockCircuit.bitsValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.update_of_ne (L.tag_b t i).symm]


















theorem action_tags (x : Basis n) (hx : ∀ t, x (L.tags t) = false) (t : Fin 5) :
    L.action x (L.tags t) = L.truth x t := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  fin_cases t <;>
    simp [action,program,CleanProgram.append,constProgram,flipProgram,varProgram,constAction,
      xAction,Function.comp_apply,L.aValue_update,L.bValue_update,
      VariableEquality.comparisonBit_update L.cmp _ _ _ (L.tag_cmp _),
      L.tags.injective.eq_iff,h0,h1,h2,h3,h4,truth]

theorem action_outside_tags (x : Basis n) (w : Fin n) (hw : ∀ t, w ≠ L.tags t) :
    L.action x w = x w := by
  simp [action,program,CleanProgram.append,constProgram,flipProgram,varProgram,constAction,
    xAction,Function.comp_apply,Function.update_of_ne,hw]



/-- Threshold-source contracts turn the five physical tags into exact validity. -/
theorem truth_iff_valid (V : Verifier gatesG2) (hk : k = indexQubits V) (hk3 : 3≤k)
    (x : Basis n) (ha : L.aValue x < 2^k) (hb : L.bValue x < 2^k)
    (hc : littleValue (x ∘ leftWire L.cmp) = L.aValue x)
    (hd : littleValue (x ∘ rightWire L.cmp) = 2*L.bValue x) :
    (∀ t, L.truth x t = true) ↔ IsValidCertificate V (L.aValue x) (L.bValue x) := by
  have ht : L.truth x = checks k (L.aValue x) (L.bValue x) := by
    funext t
    fin_cases t <;> simp [truth,checks,VariableEquality.comparisonBit,hc,hd]
  rw [ht]
  subst k
  exact checks_iff_valid V _ _ hk3 ha hb







theorem conjunction_eq_valid (V : Verifier gatesG2) (hk : k = indexQubits V) (hk3 : 3≤k)
    (x : Basis n) (hx : ∀ t, x (L.tags t) = false)
    (ha : L.aValue x < 2^k) (hb : L.bValue x < 2^k)
    (hc : littleValue (x ∘ leftWire L.cmp) = L.aValue x)
    (hd : littleValue (x ∘ rightWire L.cmp) = 2*L.bValue x) :
    prefixAnd (L.conjunctionLayout hk3) (L.action x) 5 le_rfl =
      decide (IsValidCertificate V (L.aValue x) (L.bValue x)) := by
  apply Bool.eq_iff_iff.mpr
  rw [prefixAnd_eq_true,decide_eq_true_eq]
  have he : (∀ j : Fin 5, j.val<5 → L.action x ((L.conjunctionLayout hk3).controls j) = true) ↔
      (∀ j, L.truth x j = true) := by
    simp only [conjunctionLayout,L.action_tags x hx]
    exact ⟨fun h j => h j j.isLt,fun h j _ => h j⟩
  rw [he,L.truth_iff_valid V hk hk3 x ha hb hc hd]

/-- Exact validity toggle; criterion tags may remain as explicitly retained ancillary data. -/
theorem validProgram_matrix (V : Verifier gatesG2) (hk : k = indexQubits V) (hk3 : 3≤k)
    (out : Fin n) (hot : ∀ t, out ≠ L.tags t) (hoa : ∀ j, out ≠ L.a.flags j)
    (hob : ∀ j, out ≠ L.b.flags j) (hoc : ∀ j, out ≠ L.cmp j)
    (y x : Basis n) (hclean : L.Clean x) (hx : ∀ t, x (L.tags t) = false)
    (ha : L.aValue x < 2^k) (hb : L.bValue x < 2^k)
    (hc : littleValue (x ∘ leftWire L.cmp) = L.aValue x)
    (hd : littleValue (x ∘ rightWire L.cmp) = 2*L.bValue x) :
    circuitMatrix (L.validProgram hk3 out hot hoa hob hoc).gates y x =
      if y = Function.update (L.action x) out
        (xor (x out) (decide (IsValidCertificate V (L.aValue x) (L.bValue x)))) then 1 else 0 := by
  rw [(L.validProgram hk3 out hot hoa hob hoc).sound y x hclean]
  change (if y = Function.update (L.action x) out
    (xor (L.action x out) (prefixAnd (L.conjunctionLayout hk3) (L.action x) 5 le_rfl)) then (1 : ℂ) else 0) = _
  rw [L.action_outside_tags x out hot,L.conjunction_eq_valid V hk hk3 x hx ha hb hc hd]



end Layout
end QMAPerfectCompleteness.Main.CertificateValidity

end

/- Inline helpers retained from Solutions.RegisterCopies. -/
section


/-! Parallel classical register copies with distinct targets and unchanged source wires. -/
namespace QMAPerfectCompleteness.Main.RegisterCopies
open BooleanCircuits

variable {ι : Type*} [DecidableEq ι] {n : ℕ}
variable (source : ι → Fin n) (target : ι ↪ Fin n)
variable (hd : ∀ i j, source i ≠ target j)





lemma commands_target (js : List ι) (c : Command n) (hc : c ∈ commands source target hd js) :
    ∃ j ∈ js, c.target = target j := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
  exact ⟨j,hj,rfl⟩

theorem eval_outside (js : List ι) (x : Basis n) (w : Fin n)
    (hw : ∀ j ∈ js, w ≠ target j) : eval (commands source target hd js) x w = x w := by
  apply BooleanCircuits.eval_outside
  intro c hc
  obtain ⟨j,hj,ht⟩ := commands_target source target hd js c hc
  rw [ht]
  exact hw j hj







end QMAPerfectCompleteness.Main.RegisterCopies

end

/- Inline helpers retained from Solutions.ThresholdPreparation. -/
section


/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits





namespace Layout
variable {k n : ℕ} (L : Layout k n)





























theorem copies_outside (x : Basis n) (w : Fin n) (hw : ∀ i, w ≠ L.target i) :
    L.copyState x w = x w :=
  RegisterCopies.eval_outside L.source L.targetEmbedding L.source_ne_target _ x w (fun i _ => hw i)






























theorem gates_matrix : circuitMatrix L.gates = classicalMatrix (eval L.commands) := compile_matrix _

lemma three_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 4 j)) :
    eval L.three.commands x w = x w := by
  apply L.three.commands_frame
  intro j
  rw [L.three_output]
  exact hw j

lemma upper_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 5 j)) :
    eval L.upper.commands x w = x w := by
  apply L.upper.commands_frame
  intro j
  rw [L.upper_output]
  exact hw j













lemma state_eq (x : Basis n) : L.state x =
    eval L.upper.commands (eval L.three.commands (L.copyState x)) := by
  rw [state,commands,VariableAddition.eval_append,VariableAddition.eval_append]
  rfl

/-- Every wire outside the six threshold words is restored, including the certificate and
shared arithmetic scratch. This also frames arbitrary quantum body registers. -/
theorem state_outside (x : Basis n) (w : Fin n) (hw : ∀ d j, w ≠ L.wire (.word d j)) :
    L.state x w = x w := by
  rw [state_eq,L.upper_outside _ _ (hw 5),L.three_outside _ _ (hw 4)]
  apply L.copies_outside
  intro i
  exact hw _ _















end Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation

end

/- Inline helpers retained from Solutions.CertificateThresholdLayout. -/
section


/-! The actual master-layout placement of the coherent binary threshold preparation. -/
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open ThresholdPreparation










@[simp] theorem thresholdWire_word (V : Verifier gatesG2) (s : Fin 6) (j : Fin (r V)) :
    thresholdWire V (.word s j) = prepWord V s j := rfl
@[simp] theorem thresholdWire_carry (V : Verifier gatesG2) (j : Fin (k V+3)) :
    thresholdWire V (.carry j) = prepCarry V j := rfl
@[simp] theorem thresholdWire_temp (V : Verifier gatesG2) : thresholdWire V .temp = prepTemp V := rfl

end QMAPerfectCompleteness.Main.CertificateMasterLayout

end

/- Inline helpers retained from Solutions.CertificatePreparation. -/
section


/-! Actual threshold preparation on the physical coherent verifier, with a certificate-only
workspace fiber. The arithmetic garbage may be retained throughout the quantum block. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits
variable (V : Verifier gatesG2)






@[simp] theorem coords_raw (p : Logical V) : coords V (rawEncoding V p) = (p,fun _=>false) :=
  (coords V).apply_symm_apply _





lemma raw_work (p : Logical V) (i : Fin (work V)) : rawEncoding V p (workWire V i)=false := by
  have h := congrFun (congrArg Prod.snd (coords_raw V p)) i
  exact h

lemma raw_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val < bodyWires V+work V) : rawEncoding V p w=false := by
  let i : Fin (work V) := ⟨w.val-bodyWires V,by omega⟩
  have he : workWire V i=w := Fin.ext (by change bodyWires V+(w.val-bodyWires V)=w.val; omega)
  rw [← he,raw_work]




@[simp] lemma thresholdLayout_wire : (thresholdLayout V).wire = thresholdWire V := rfl




lemma word_work (d : Fin 6) (j : Fin (r V)) :
    bodyWires V ≤ (prepWord V d j).val ∧ (prepWord V d j).val < bodyWires V+work V := by
  have h := CertificateRangeCircuit.word_bounds V d j
  have hm : oldWork V+6*r V ≤ work V := by dsimp only [work,prepWork,r,k]; omega
  dsimp only [r,k] at h hm ⊢
  omega

lemma carry_work (j : Fin (k V+3)) :
    bodyWires V ≤ (prepCarry V j).val ∧ (prepCarry V j).val < bodyWires V+work V := by
  have hj := j.isLt
  change bodyWires V ≤ bodyWires V+(oldWork V+6*r V)+j.val ∧ _
  change _ ∧ bodyWires V+(oldWork V+6*r V)+j.val < bodyWires V+work V
  dsimp [work,prepWork,r,k] at *
  omega

lemma temp_work : bodyWires V ≤ (prepTemp V).val ∧ (prepTemp V).val < bodyWires V+work V := by
  change bodyWires V ≤ bodyWires V+(oldWork V+6*r V+(k V+3))+0 ∧ _
  change _ ∧ bodyWires V+(oldWork V+6*r V+(k V+3))+0 < bodyWires V+work V
  dsimp [work,prepWork,r,k]
  omega

lemma raw_clean (p : Logical V) : (thresholdLayout V).Clean (rawEncoding V p) := by
  refine ⟨?_,?_,?_⟩
  · intro d j
    rw [thresholdLayout_wire,thresholdWire_word]
    exact raw_at_work V p _ (word_work V d j).1 (word_work V d j).2
  · intro j
    rw [thresholdLayout_wire,thresholdWire_carry]
    exact raw_at_work V p _ (carry_work V j).1 (carry_work V j).2
  · rw [thresholdLayout_wire,thresholdWire_temp]
    exact raw_at_work V p _ (temp_work V).1 (temp_work V).2

lemma prep_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val < bodyWires V+work V)
    (hn : ∀ d j, w ≠ prepWord V d j) : prepState V (rawEncoding V p) w=false := by
  rw [prepState,ThresholdPreparation.Layout.state_outside]
  · exact raw_at_work V p w hw0 hw1
  · simpa only [thresholdLayout_wire,thresholdWire_word] using hn

lemma prep_data (x : Physical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prepState V x w=x w := by
  apply (thresholdLayout V).state_outside
  intro d j h
  rw [thresholdLayout_wire,thresholdWire_word] at h
  have hh := congrArg Fin.val h
  have hb := word_work V d j
  omega








/-- Exact literal matrix column, including all arithmetic garbage. -/
theorem prep_matrix (y : Physical V) (p : Logical V) :
    circuitMatrix (prepGates V) y (rawEncoding V p) =
      if y=prepState V (rawEncoding V p) then 1 else 0 := by
  rw [prepGates,ThresholdPreparation.Layout.gates_matrix]
  rfl

end QMAPerfectCompleteness.Main.CertificatePreparation

end

/- Inline helpers retained from Solutions.CertificateClaimBits. -/
section


/-! Physical certificate bits are the published little-endian z,a,b coordinates. -/
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
open CertificateMasterLayout CertificateCoordinates BlockCircuit IndexHadamards
variable (V : Verifier gatesG2)

lemma certificate_zero (j : Fin (k V)) : certificate V 0 j =
    Fin.natAdd (bodyWires V+work V) (Fin.natAdd V.proofQubits (Fin.castAdd (k V) j)) := by
  apply Fin.ext
  simp [certificate,certAB,finProdFinEquiv,k,Nat.add_assoc]

lemma certificate_one (j : Fin (k V)) : certificate V 1 j =
    Fin.natAdd (bodyWires V+work V) (Fin.natAdd V.proofQubits (Fin.natAdd (k V) j)) := by
  apply Fin.ext
  simp [certificate,certAB,finProdFinEquiv,k,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- No modulus or truncation is hidden in the certificate's natural-number reading. -/
theorem a_value (x : Basis (total V)) :
    ComparisonCircuits.littleValue (fun j => x (certificate V 0 j)) =
      (computationEquiv V (work V) x).1.2.2.1.val := by
  simp_rw [certificate_zero]
  rfl

theorem b_value (x : Basis (total V)) :
    ComparisonCircuits.littleValue (fun j => x (certificate V 1 j)) =
      (computationEquiv V (work V) x).1.2.2.2.val := by
  simp_rw [certificate_one]
  rfl



end QMAPerfectCompleteness.Main.CertificateClaimBits

end

/- Inline helpers retained from Solutions.CertificateValidityPreparation. -/
section


/-! The actual arithmetic-plus-validity prefix and its certificate-dependent workspace fiber. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits CertificateValidityCircuit
variable (V : Verifier gatesG2)



lemma validity_work (t : Fin 6) :
    bodyWires V ≤ (validity V t).val ∧ (validity V t).val < bodyWires V+work V := by
  have ht := t.isLt
  change bodyWires V ≤ bodyWires V+(oldWork V+prepWork V+2)+t.val ∧ _
  change _ ∧ bodyWires V+(oldWork V+prepWork V+2)+t.val < bodyWires V+work V
  dsimp only [work]
  omega

lemma data_ne_validity (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) (t : Fin 6) : w ≠ validity V t := by
  intro h
  have ht := validity_work V t
  have hv := congrArg Fin.val h
  omega

lemma prep_validity (p : Logical V) (t : Fin 6) : prepState V (rawEncoding V p) (validity V t)=false := by
  apply prep_at_work V p _ (validity_work V t).1 (validity_work V t).2
  intro d j
  exact validity_ne_word V t d j

lemma prep_scratch (p : Logical V) (j : Fin (r V+2)) :
    prepState V (rawEncoding V p) (CertificateRangeCircuit.scratch V j)=false := by
  have hs := CertificateRangeCircuit.scratch_bounds V j
  have hm : oldWork V+prepWork V ≤ work V := by dsimp only [work]; omega
  apply prep_at_work V p
  · omega
  · omega
  · intro d i h
    have hw := CertificateRangeCircuit.word_bounds V d i
    have hv := congrArg Fin.val h
    omega

lemma prep_carry (p : Logical V) (j : Fin (k V+3)) :
    prepState V (rawEncoding V p) (prepCarry V j)=false := by
  apply prep_at_work V p _ (carry_work V j).1 (carry_work V j).2
  intro d i h
  have hw := CertificateRangeCircuit.word_bounds V d i
  have hv := congrArg Fin.val h
  change (prepCarry V j).val = (prepWord V d i).val at hv
  change bodyWires V+(oldWork V+6*r V)+j.val = (prepWord V d i).val at hv
  omega

lemma prep_validity_clean (p : Logical V) : (CertificateValidityCircuit.layout V).Clean (prepState V (rawEncoding V p)) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact prep_carry V p j
  · intro j
    exact prep_carry V p j
  · constructor
    · intro j
      change prepState V (rawEncoding V p)
        (VariableComparison.carryWire ((comparatorWires V).comparator 0) j)=false
      rw [DynamicBlockCompiler.RangeWires.comparator_carry]
      exact prep_scratch V p _
    · change prepState V (rawEncoding V p)
        (VariableComparison.tempWire ((comparatorWires V).comparator 0))=false
      rw [DynamicBlockCompiler.RangeWires.comparator_temp]
      exact prep_scratch V p _

lemma raw_a (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 0=p.2.2.1.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 0 j)) = _
  rw [CertificateClaimBits.a_value,coords_raw]
lemma raw_b (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 1=p.2.2.2.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 1 j)) = _
  rw [CertificateClaimBits.b_value,coords_raw]

lemma prep_values (p : Logical V) (d : Fin 6) :
    littleValue (fun j => prepState V (rawEncoding V p) (prepWord V d j)) =
      (![p.2.2.1.val,2*p.2.2.1.val,p.2.2.2.val,2*p.2.2.2.val,
        3*p.2.2.1.val,3*p.2.2.1.val+p.2.2.2.val] : Fin 6 → ℕ) d := by
  have h := (thresholdLayout V).values (rawEncoding V p) (raw_clean V p) d
  rw [raw_a,raw_b] at h
  simpa only [prepState,thresholdLayout_wire,thresholdWire_word] using h

lemma prep_aValue (p : Logical V) :
    (CertificateValidityCircuit.layout V).aValue (prepState V (rawEncoding V p)) = p.2.2.1.val := by
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 0 j)) = _
  simpa using prep_values V p 0
lemma prep_bValue (p : Logical V) :
    (CertificateValidityCircuit.layout V).bValue (prepState V (rawEncoding V p)) = p.2.2.2.val := by
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 2 j)) = _
  simpa using prep_values V p 2

lemma prep_cmp_left (p : Logical V) :
    littleValue ((prepState V (rawEncoding V p)) ∘ VariableComparison.leftWire (CertificateValidityCircuit.layout V).cmp) = p.2.2.1.val := by
  simp only [Function.comp_def,show (CertificateValidityCircuit.layout V).cmp = (comparatorWires V).comparator 0 from rfl]
  simp_rw [DynamicBlockCompiler.RangeWires.comparator_left]
  exact prep_aValue V p

lemma prep_cmp_right (p : Logical V) :
    littleValue ((prepState V (rawEncoding V p)) ∘ VariableComparison.rightWire (CertificateValidityCircuit.layout V).cmp) = 2*p.2.2.2.val := by
  simp only [Function.comp_def,show (CertificateValidityCircuit.layout V).cmp = (comparatorWires V).comparator 0 from rfl]
  simp_rw [DynamicBlockCompiler.RangeWires.comparator_right]
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 3 j)) = _
  simpa using prep_values V p 3





lemma prefix_data (p : Logical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prefixEncoding V p w=rawEncoding V p w := by
  rw [prefixEncoding,Function.update_of_ne (data_ne_validity V w hw 5)]
  rw [CertificateValidity.Layout.action_outside_tags]
  · exact prep_data V _ _ hw
  · intro t
    exact data_ne_validity V w hw ⟨t.val,by have := t.isLt; omega⟩

lemma prefix_logical (p : Logical V) : (coords V (prefixEncoding V p)).1=p := by
  rw [logical_eq_of_data V _ (rawEncoding V p) (prefix_data V p),coords_raw]

lemma prefix_valid (p : Logical V) : prefixEncoding V p (validity V 5) =
    decide (IsValidCertificate V p.2.2.1.val p.2.2.2.val) := by
  simp only [prefixEncoding,Function.update_self]







/-- Exact physical prefix column on the initialized encoding. -/
theorem prefix_matrix (y : Physical V) (p : Logical V) :
    circuitMatrix (prefixGates V) y (rawEncoding V p) = if y=prefixEncoding V p then 1 else 0 := by
  rw [prefixGates,BlockProof.circuitMatrix_append]
  simp only [Matrix.mul_apply,prep_matrix]
  rw [Finset.sum_eq_single (prepState V (rawEncoding V p))]
  · simp only [if_true,mul_one]
    have h := (CertificateValidityCircuit.layout V).validProgram_matrix V rfl (index_width V)
      (validity V 5) (output_ne_tags V) (validity_ne_carry V 5) (validity_ne_carry V 5)
      ((comparatorWires V).toLayout.disjoint 5 0) y (prepState V (rawEncoding V p))
      (prep_validity_clean V p)
      (fun t => prep_validity V p ⟨t.val,by have := t.isLt; omega⟩)
      (by rw [prep_aValue]; exact p.2.2.1.isLt) (by rw [prep_bValue]; exact p.2.2.2.isLt)
      (by rw [prep_cmp_left,prep_aValue]) (by rw [prep_cmp_right,prep_bValue])
    simpa only [CertificateValidityCircuit.gates,CertificateValidityCircuit.program,
      prep_aValue,prep_bValue,prep_validity,Bool.false_xor,prefixEncoding] using h
  · intro z _ hz
    simp [hz]
  · simp

end QMAPerfectCompleteness.Main.CertificatePreparation

end

/- Inline helpers retained from Solutions.CertificatePreparedFacts. -/
section


/-! Concrete readiness facts for the quantum block and final readout after certificate prep. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits CertificateValidityCircuit
variable (V : Verifier gatesG2)

/-- Only threshold words and the six validity bits may be nonzero in prepared workspace. -/
theorem prefix_at_work (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V ≤ w.val) (hw1 : w.val<bodyWires V+work V)
    (hn : ∀ d j, w ≠ prepWord V d j) (hv : ∀ t, w ≠ validity V t) :
    prefixEncoding V p w=false := by
  rw [prefixEncoding,Function.update_of_ne (hv 5),CertificateValidity.Layout.action_outside_tags]
  · exact prep_at_work V p w hw0 hw1 hn
  · intro t
    exact hv ⟨t.val,by have := t.isLt; omega⟩





theorem prefix_injective : Function.Injective (prefixEncoding V) := by
  intro p q h
  have he := congrArg (fun z => (coords V z).1) h
  simpa only [prefix_logical] using he



lemma prefix_after_validity (p : Logical V) (w : Fin (total V))
    (hw0 : bodyWires V+oldWork V+prepWork V+8 ≤ w.val)
    (hw1 : w.val<bodyWires V+work V) : prefixEncoding V p w=false := by
  apply prefix_at_work V p w (by omega) hw1
  · intro d j h
    have hv := congrArg Fin.val h
    have hb := CertificateRangeCircuit.word_bounds V d j
    have hh : 6*r V ≤ prepWork V := by dsimp only [prepWork,r,k]; omega
    omega
  · intro t h
    have hv := congrArg Fin.val h
    have ht := t.isLt
    change w.val=bodyWires V+(oldWork V+prepWork V+2)+t.val at hv
    omega

/-- All flags for the readout zero-test still start in zero. -/
theorem prefix_readout_flags (p : Logical V) (j : Fin (readoutWork V)) :
    prefixEncoding V p (readoutFlags V j)=false := by
  apply prefix_after_validity V p
  · change bodyWires V+oldWork V+prepWork V+8 ≤
      bodyWires V+(oldWork V+prepWork V+2+6)+j.val
    omega
  · have hj := j.isLt
    change bodyWires V+(oldWork V+prepWork V+2+6)+j.val<bodyWires V+work V
    dsimp only [work]
    omega

/-- Both the readout zero-test bit and accepting output bit remain clean. -/
theorem prefix_readout_tags (p : Logical V) (j : Fin 2) :
    prefixEncoding V p (readoutTags V j)=false := by
  apply prefix_after_validity V p
  · change bodyWires V+oldWork V+prepWork V+8 ≤
      bodyWires V+(oldWork V+prepWork V+2+6+readoutWork V)+j.val
    omega
  · have hj := j.isLt
    change bodyWires V+(oldWork V+prepWork V+2+6+readoutWork V)+j.val<bodyWires V+work V
    dsimp only [work]
    omega

end QMAPerfectCompleteness.Main.CertificatePreparation

end

/- Inline helpers retained from Solutions.CertificateInitialization. -/
section


/-! Exact initialized history/certificate registers in the physical coherent-verifier layout. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateInitialization
open CertificateCoordinates CertificateVerifierLayout BlockCircuit BlockCoordinates

variable (V : Verifier gatesG2) (w : ℕ)







lemma prepared_index_bits (p : Basis (proofQubits V)) (i : Fin (indexQubits V)) :
    prepared V w p (Fin.castAdd (claimQubits V) (indexWire (w:=w) i)) = false := by
  exact prepared_index V w p i
lemma prepared_clock_bits (p : Basis (proofQubits V)) (i : Fin (clockWires V)) :
    prepared V w p (Fin.castAdd (claimQubits V) (clockWire (w:=w) i)) = clockBits V p i := by
  change prepared V w p (physicalHistory V w (Fin.castAdd V.proofQubits i)) = _
  rw [prepared_history]
  rfl

lemma prepared_verifier_bits (p : Basis (proofQubits V)) (i : Fin (V.proofQubits+V.ancillaQubits)) :
    prepared V w p (Fin.castAdd (claimQubits V) (verifierWire (w:=w) i)) =
      V.initialState (proofBits V p) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have ha : Fin.castAdd (claimQubits V) (verifierWire (w:=w) (Fin.castAdd V.ancillaQubits j)) =
        physicalHistory V w (Fin.natAdd (clockWires V) j) := by
      apply Fin.ext
      simp [verifierWire,physicalHistory,Nat.add_assoc]
    rw [ha,prepared_history]
    simp only [Verifier.initialState,Fin.append_left]
    rfl
  · have ha : Fin.castAdd (claimQubits V) (verifierWire (w:=w) (Fin.natAdd V.proofQubits j)) =
        physicalAncilla V w ⟨j.val,by have := j.isLt; omega⟩ := by
      apply Fin.ext
      simp [verifierWire,physicalAncilla,Nat.add_assoc]
    rw [ha,prepared_ancilla]
    simp [Verifier.initialState]

lemma prepared_flag (p : Basis (proofQubits V)) :
    prepared V w p (Fin.castAdd (claimQubits V) (flagWire (V:=V) (w:=w))) = false := by
  have ha : Fin.castAdd (claimQubits V) (flagWire (V:=V) (w:=w)) =
      physicalAncilla V w ⟨V.ancillaQubits,by omega⟩ := by
    apply Fin.ext
    simp [flagWire,physicalAncilla,Nat.add_assoc]
  rw [ha,prepared_ancilla]

lemma prepared_work (p : Basis (proofQubits V)) (i : Fin w) :
    prepared V w p (Fin.castAdd (claimQubits V) (workspaceWire (V:=V) i)) = false := by
  have ha : Fin.castAdd (claimQubits V) (workspaceWire (V:=V) i) =
      physicalAncilla V w ⟨V.ancillaQubits+1+i.val,by have := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [workspaceWire,bodyWires,physicalAncilla,Nat.add_assoc]
  rw [ha,prepared_ancilla]

/-- Actual all-zero verifier ancillas give zero index/Y/flag/work and the untouched coherent
certificate, with the history exactly in the intended proof coordinates. -/
theorem prepared_coordinates (p : Basis (proofQubits V)) :
    computationEquiv V w (prepared V w p) =
      (logicalInitial V false (proofEquiv V p),fun _=>false) := by
  let x : Basis (bodyWires V+w) := fun i => prepared V w p (Fin.castAdd (claimQubits V) i)
  have hi : ∀ i, x (indexWire i)=false := prepared_index_bits V w p
  have hc : x ∘ clockWire = clockBits V p := funext (prepared_clock_bits V w p)
  have hv : x ∘ verifierWire = V.initialState (proofBits V p) := funext (prepared_verifier_bits V w p)
  have hf : x flagWire=false := prepared_flag V w p
  apply Prod.ext
  · apply Prod.ext
    · rw [computationEquiv_body]
      change decode x = _
      apply Prod.ext
      · change Fin.ofNat (2^indexQubits V) (bitsValue x indexWire) = 0
        simp [bitsValue,hi]
      · apply Prod.ext
        · change Fin.ofNat (ell V.proofQubits+1) (bitsValue x clockWire) = clockEquiv V (clockBits V p)
          apply Fin.ext
          change bitsValue x clockWire % (ell V.proofQubits+1) = ComparisonCircuits.littleValue (clockBits V p)
          have hbits : bitsValue x clockWire = ComparisonCircuits.littleValue (clockBits V p) :=
            congrArg ComparisonCircuits.littleValue hc
          rw [hbits,clock_card]
          exact Nat.mod_eq_of_lt (ComparisonCircuits.littleValue_lt_two_pow _)
        · exact Prod.ext hv hf
    · rw [computationEquiv_claim]
      change claimEquiv V (fun i => prepared V w p (physicalClaim V w i)) = claimEquiv V (claimBits V p)
      congr 1
      funext i
      exact prepared_claim V w p i
  · rw [computationEquiv_work]
    funext i
    exact prepared_work V w p i



lemma index_ne_physicalFlag (i : Fin (indexQubits V)) :
    Fin.castAdd (claimQubits V) (indexWire (w:=w) i) ≠ physicalFlag V w := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change i.val=indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
  omega
lemma clock_ne_physicalFlag (i : Fin (clockWires V)) :
    Fin.castAdd (claimQubits V) (clockWire (w:=w) i) ≠ physicalFlag V w := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change indexQubits V+i.val=indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
  omega
lemma verifier_ne_physicalFlag (i : Fin (V.proofQubits+V.ancillaQubits)) :
    Fin.castAdd (claimQubits V) (verifierWire (w:=w) i) ≠ physicalFlag V w := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change indexQubits V+clockWires V+i.val=indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
  omega
lemma workspace_ne_physicalFlag (i : Fin w) :
    Fin.castAdd (claimQubits V) (workspaceWire (V:=V) i) ≠ physicalFlag V w := by
  intro h
  have hv := congrArg Fin.val h
  change bodyWires V+i.val=indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
  dsimp only [bodyWires] at hv
  omega
lemma claim_ne_physicalFlag (i : Fin (claimQubits V)) :
    physicalClaim V w i ≠ physicalFlag V w := by
  intro h
  have hv := congrArg Fin.val h
  change bodyWires V+w+i.val=indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) at hv
  dsimp only [bodyWires] at hv
  omega

set_option maxHeartbeats 1200000 in
lemma computation_update_flag (x : Basis ((bodyWires V+w)+claimQubits V)) (b : Bool) :
    computationEquiv V w (Function.update x (physicalFlag V w) b) =
      ((((computationEquiv V w x).1.1.1,(computationEquiv V w x).1.1.2.1,
        (computationEquiv V w x).1.1.2.2.1,b),(computationEquiv V w x).1.2),
        (computationEquiv V w x).2) := by
  apply Prod.ext
  · apply Prod.ext
    · rw [computationEquiv_body,computationEquiv_body]
      apply Prod.ext
      · change Fin.ofNat _ (bitsValue (fun i => Function.update x (physicalFlag V w) b
          (Fin.castAdd (claimQubits V) i)) indexWire) =
          Fin.ofNat _ (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) indexWire)
        congr 1
        unfold bitsValue
        simp_rw [Function.update_of_ne (index_ne_physicalFlag V w _)]
      · apply Prod.ext
        · change Fin.ofNat _ (bitsValue (fun i => Function.update x (physicalFlag V w) b
            (Fin.castAdd (claimQubits V) i)) clockWire) =
            Fin.ofNat _ (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) clockWire)
          congr 1
          unfold bitsValue
          simp_rw [Function.update_of_ne (clock_ne_physicalFlag V w _)]
        · apply Prod.ext
          · funext i
            exact Function.update_of_ne (verifier_ne_physicalFlag V w i) b x
          · exact Function.update_self _ _ _
    · rw [computationEquiv_claim,computationEquiv_claim]
      congr 1
      funext i
      exact Function.update_of_ne (claim_ne_physicalFlag V w i) b x
  · rw [computationEquiv_work,computationEquiv_work]
    funext i
    exact Function.update_of_ne (workspace_ne_physicalFlag V w i) b x



/-- One actual X gate converts the published zero-ancilla initialization to η. -/
theorem prepare_eta (p : Basis (proofQubits V)) :
    ReversibleGadgets.xAction (physicalFlag V w) (prepared V w p) = etaState V w p := by
  unfold ReversibleGadgets.xAction
  have hf : prepared V w p (physicalFlag V w) = false := prepared_flag V w p
  rw [hf]
  apply (computationEquiv V w).injective
  rw [computation_update_flag,prepared_coordinates]
  simp [etaState,logicalInitial]

end QMAPerfectCompleteness.Main.CertificateInitialization

end

/- Inline helpers retained from Solutions.CoherentAcceptance. -/
section


/-! Exact acceptance algebra for retained certificate fibers and ignored ancillary garbage. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture
attribute [local instance] QMAPerfectCompleteness.Main.CoherentCertificate.computationDecEq

lemma initialIsometry_gram (V : Verifier gatesG2) : (initialIsometry V)ᴴ * initialIsometry V = 1 := by
  rw [initialIsometry,Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
  simp only [zEmbed_isometry]
  exact Matrix.blockDiagonal_one

/-- No validity control on the quantum block is needed: invalid branches are unitary and
rejected by the final readout; valid branches implement the paper's exact block operator. -/
theorem acceptance_effect_of_unitary_branches (V : Verifier gatesG2)
    (U : Claim V → Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ)
    (hvalid : ∀ c, IsValidCertificate V c.2.1 c.2.2 →
      U c = V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2)
    (hunitary : ∀ c, (U c)ᴴ * U c = 1) :
    (initialIsometry V)ᴴ * (Matrix.blockDiagonal U)ᴴ * (1-rejectProjector V) *
      Matrix.blockDiagonal U * initialIsometry V = 1-Matrix.blockDiagonal (claimRejection V) := by
  classical
  let M := Matrix.blockDiagonal U
  let J := initialIsometry V
  have hM : Mᴴ * M = 1 := by
    rw [Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
    simp only [hunitary]
    ext ⟨p,c⟩ ⟨q,d⟩
    by_cases hc : c=d <;> by_cases hp : p=q <;>
      simp [Matrix.blockDiagonal_apply,Matrix.one_apply,Prod.mk.injEq,hc,hp]
  have hin : Mᴴ * (1-rejectProjector V) * M = 1-Mᴴ * rejectProjector V * M := by
    rw [Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul,hM]
  have hR : Jᴴ * (Mᴴ * rejectProjector V * M) * J = Matrix.blockDiagonal (claimRejection V) := by
    simpa only [Matrix.mul_assoc] using rejection_effect_of_unitary_branches V U hvalid (fun c _ => hunitary c)
  calc
    _ = Jᴴ * (Mᴴ * (1-rejectProjector V) * M) * J := by
      simp only [Matrix.mul_assoc]
      rfl
    _ = Jᴴ * (1-Mᴴ*rejectProjector V*M) * J := by rw [hin]
    _ = Jᴴ * J - Jᴴ * (Mᴴ*rejectProjector V*M) * J := by
      rw [Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul]
    _ = 1-Matrix.blockDiagonal (claimRejection V) := by rw [hR,initialIsometry_gram]

/-- An actual unitary circuit transporting two isometric basis encodings forces the logical
matrix to be an isometry. This also applies to invalid-certificate branches. -/
theorem gram_of_transport {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (C : Matrix β β ℂ) (K L : Matrix β α ℂ) (U : Matrix α α ℂ)
    (hC : Cᴴ*C=1) (hK : Kᴴ*K=1) (hL : Lᴴ*L=1) (htrans : C*K=L*U) : Uᴴ*U=1 := by
  calc
    Uᴴ*U = Uᴴ*(Lᴴ*L)*U := by rw [hL,Matrix.mul_one]
    _ = (L*U)ᴴ*(L*U) := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = (C*K)ᴴ*(C*K) := by rw [htrans]
    _ = Kᴴ*(Cᴴ*C)*K := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [hC,Matrix.mul_one,hK]



end QMAPerfectCompleteness.Main.CoherentCertificate

end

/- Inline helpers retained from Solutions.CoherentReadout. -/
section


/-! Exact matrix compression of a final Boolean readout flag and the all-zero Z projector. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture



lemma basis_diagonal_compression {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α → β) (he : Function.Injective e) (d : β → ℂ) :
    (basisMatrix e)ᴴ * Matrix.diagonal d * basisMatrix e = Matrix.diagonal (d ∘ e) := by
  ext y x
  simp [basisMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
    mul_ite,ite_mul,he.eq_iff,eq_comm]
  split_ifs with h
  · subst x; rfl
  · rfl

/-- A physical clean readout column determines its full logical acceptance effect. -/
theorem flag_readout_compression {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (e : α → Basis n) (he : Function.Injective e) (out : Fin n) (a : α → Bool)
    (hzero : ∀p,e p out=false) (C : Matrix (Basis n) (Basis n) ℂ)
    (hC : ∀ y p, C y (e p)=if y=Function.update (e p) out (a p) then 1 else 0) :
    (basisMatrix e)ᴴ * Cᴴ * Matrix.diagonal (fun x : Basis n => if x out then (1:ℂ) else 0) * C * basisMatrix e =
      Matrix.diagonal (fun p => if a p then (1:ℂ) else 0) := by
  classical
  let f : α → Basis n := fun p => Function.update (e p) out (a p)
  have hf : Function.Injective f := by
    intro p q h
    have hreset (p) : Function.update (e p) out false=e p := by
      rw [← hzero p]
      exact Function.update_eq_self _ _
    have hr := congrArg (fun x => Function.update x out false) h
    simp only [f,Function.update_idem,hreset] at hr
    exact he hr
  have ht : C * basisMatrix e = basisMatrix f := by
    ext y p
    by_cases hy : y=Function.update (e p) out (a p) <;>
      simp [basisMatrix,Matrix.mul_apply,mul_ite,hC,f,hy]
  calc
    _ = (C*basisMatrix e)ᴴ * Matrix.diagonal (fun x : Basis n => if x out then (1:ℂ) else 0) * (C*basisMatrix e) := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = (basisMatrix f)ᴴ * Matrix.diagonal (fun x : Basis n => if x out then (1:ℂ) else 0) * basisMatrix f := by rw [ht]
    _ = _ := by
      rw [basis_diagonal_compression f hf]
      simp [f,Function.comp_def]





lemma zeroZ_iff (V : Verifier gatesG2) (p : V.BlockReg (indexQubits V)) :
    zeroZ V p ↔ p.1=0 ∧ p.2.2.1=V.initialState (V.proofPart p.2.2.1) ∧ p.2.2.2=false := by
  constructor
  · rintro ⟨h,rfl⟩
    simp [BlockProof.bodyInitial,BlockProof.proofPart_initialState]
  · rintro ⟨hi,hw,hf⟩
    refine ⟨(p.2.1,V.proofPart p.2.2.1),?_⟩
    exact Prod.ext hi (Prod.ext rfl (Prod.ext hw hf))

set_option maxHeartbeats 2000000 in
theorem zEmbed_projector (V : Verifier gatesG2) :
    V.zEmbed (indexQubits V) false * (V.zEmbed (indexQubits V) false)ᴴ =
      Matrix.diagonal (fun p => if zeroZ V p then (1:ℂ) else 0) := by
  classical
  let e : History V → V.BlockReg (indexQubits V) := fun h => (0,BlockProof.bodyInitial V false h)
  have he : Function.Injective e := by
    intro p q h
    have hc : p.1=q.1 := congrArg (fun z : V.BlockReg (indexQubits V) => z.2.1) h
    have hw : V.initialState p.2=V.initialState q.2 :=
      congrArg (fun z : V.BlockReg (indexQubits V) => z.2.2.1) h
    exact Prod.ext hc ((BlockProof.initialState_injective V) hw)
  ext p q
  change (∑z,V.zEmbed (indexQubits V) false p z * star (V.zEmbed (indexQubits V) false q z)) = _
  by_cases hp : zeroZ V p
  · obtain ⟨h,rfl⟩ := hp
    have hrow (z : History V) : V.zEmbed (indexQubits V) false (e h) z = if z=h then 1 else 0 := by
      rw [BlockProof.zEmbed_apply]
      change (if e h=e z then (1:ℂ) else 0) = _
      by_cases hz : z=h
      · subst z; simp
      · simp [he.eq_iff,hz,Ne.symm hz]
    change (∑z,V.zEmbed (indexQubits V) false (e h) z * star (V.zEmbed (indexQubits V) false q z)) = _
    simp_rw [hrow]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [BlockProof.zEmbed_apply]
    by_cases hq : q=e h
    · subst q
      simp [e,Matrix.diagonal_apply,show zeroZ V (0,BlockProof.bodyInitial V false h) from ⟨h,rfl⟩]
    · have hq' : q≠(0,BlockProof.bodyInitial V false h) := hq
      simp [Matrix.diagonal_apply,hq',Ne.symm hq']
  · have hrow (z : History V) : V.zEmbed (indexQubits V) false p z=0 := by
      rw [BlockProof.zEmbed_apply]
      exact if_neg (fun h => hp ⟨z,h⟩)
    simp_rw [hrow]
    by_cases hq : p=q
    · subst q; simp [Matrix.diagonal_apply,hp]
    · simp [Matrix.diagonal_apply,hq]

/-- Invalid certificates reject; valid ones accept precisely off the all-zero Z subspace. -/
theorem acceptProjector_diagonal (V : Verifier gatesG2) :
    (1-rejectProjector V) = Matrix.diagonal (fun p : ComputationReg V =>
      if IsValidCertificate V p.2.2.1 p.2.2.2 ∧ ¬zeroZ V p.1 then (1:ℂ) else 0) := by
  classical
  ext ⟨p,c⟩ ⟨q,d⟩
  by_cases hc : c=d
  · subst d
    by_cases hp : p=q
    · subst q
      by_cases hv : IsValidCertificate V c.2.1 c.2.2 <;> by_cases hz : zeroZ V p <;>
        simp [rejectProjector,Matrix.blockDiagonal_apply,Matrix.diagonal_apply,
          zEmbed_projector,hv,hz]
    · by_cases hv : IsValidCertificate V c.2.1 c.2.2 <;>
        simp [rejectProjector,Matrix.blockDiagonal_apply,Matrix.diagonal_apply,
          Matrix.one_apply,hp,hv,zEmbed_projector]
  · simp [rejectProjector,Matrix.blockDiagonal_apply,Matrix.diagonal_apply,
      Matrix.one_apply,hc,Prod.ext_iff]

end QMAPerfectCompleteness.Main.CoherentCertificate

end

/- Inline helpers retained from Solutions.CertificateEtaTransport. -/
section


/-! The actual initial X gate transports initialized verifier columns to the logical η isometry. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateEtaTransport
open BlockCircuit CertificateCoordinates CertificateVerifierLayout CertificateInitialization CoherentCertificate

lemma basisMatrix_mul {α β γ : Type*} [Fintype β] (f : β → γ) (g : α → β) :
    basisMatrix f*basisMatrix g=basisMatrix (f ∘ g) := by
  classical
  ext y x
  simp [basisMatrix,Matrix.mul_apply,mul_ite]

lemma initialIsometry_basis (V : Verifier gatesG2) :
    initialIsometry V=basisMatrix (logicalInitial V true) := by
  classical
  ext ⟨body,c⟩ ⟨history,d⟩
  by_cases hc : c=d
  · subst d
    by_cases hb : body=(0,BlockProof.bodyInitial V true history) <;>
      simp [initialIsometry,Matrix.blockDiagonal_apply,BlockProof.zEmbed_apply,
        basisMatrix,logicalInitial,BlockProof.bodyInitial,Prod.mk.injEq,hb]
  · simp [initialIsometry,Matrix.blockDiagonal_apply,basisMatrix,logicalInitial,hc,Prod.mk.injEq]





/-- Exact initialized-column transport, including both physical and proof coordinates. -/
theorem eta_transport (V : Verifier gatesG2) (w : ℕ) :
    circuitMatrix (gates V w)*basisMatrix (prepared V w) =
      (basisMatrix (rawEncoding V w)*initialIsometry V).submatrix (Equiv.refl _) (proofEquiv V) := by
  rw [initialIsometry_basis,basisMatrix_mul]
  ext y p
  by_cases hy : y=etaState V w p <;>
    simp [gates,circuitMatrix,Matrix.one_mul,ReversibleGadgets.xAt_matrix,
      classicalMatrix,basisMatrix,Matrix.mul_apply,mul_ite,prepare_eta,
      Matrix.submatrix_apply,Function.comp_def,rawEncoding,etaState,hy]

end QMAPerfectCompleteness.Main.CertificateEtaTransport

end

/- Inline helpers retained from Solutions.CertificateReadoutEffect. -/
section


/-! The concrete physical Z test is exactly the paper's rejection projector. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout CoherentCertificate

lemma verifier_zero_ancillas (V : Verifier gatesG2) (x : V.Wire) :
    x=V.initialState (V.proofPart x) ↔ ∀j:Fin V.ancillaQubits,x (Fin.natAdd V.proofQubits j)=false := by
  constructor
  · intro h j
    rw [h]
    exact Fin.append_right _ _ _
  · intro h
    funext j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j
    · change x (Fin.castAdd V.ancillaQubits i)=
        (Fin.append (V.proofPart x) (fun _=>false)) (Fin.castAdd V.ancillaQubits i)
      rw [Fin.append_left]
      rfl
    · change x (Fin.natAdd V.proofQubits i)=
        (Fin.append (V.proofPart x) (fun _=>false)) (Fin.natAdd V.proofQubits i)
      rw [Fin.append_right]
      exact h i

lemma decoded_index_zero (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) :
    (decode x).1=0 ↔ ∀i,x (indexWire i)=false := by
  have he : IndexHadamards.bitsEquiv (indexQubits V) (x ∘ indexWire)=(decode x).1 :=
    congrArg Prod.fst (coordinates_fst V w x)
  have hz : IndexHadamards.bitsEquiv (indexQubits V) (fun _=>false)=0 := by
    apply Fin.ext
    simp [IndexHadamards.bitsEquiv,ComparisonCircuits.littleValue]
  rw [← he,← hz,(IndexHadamards.bitsEquiv (indexQubits V)).injective.eq_iff]
  exact ⟨fun h i=>congrFun h i,fun h=>funext h⟩

lemma decoded_zeroZ (V : Verifier gatesG2) (w : ℕ) (x : Basis (bodyWires V+w)) :
    zeroZ V (decode x) ↔ (∀i,x (indexWire i)=false) ∧
      (∀j:Fin V.ancillaQubits,x (verifierWire (Fin.natAdd V.proofQubits j))=false) ∧ x flagWire=false := by
  rw [zeroZ_iff,decoded_index_zero,verifier_zero_ancillas]
  rfl

lemma controls_index (V : Verifier gatesG2) (i : Fin (k V)) :
    zeroControls V (Fin.castAdd (V.ancillaQubits+1) i) =
      Fin.castAdd (claimQubits V) (indexWire (w:=work V) i) := by
  apply Fin.ext
  change (if i.val<k V then i.val else _) = i.val
  rw [if_pos i.isLt]

lemma controls_ancilla (V : Verifier gatesG2) (i : Fin V.ancillaQubits) :
    zeroControls V (Fin.natAdd (k V) (Fin.castAdd 1 i)) =
      Fin.castAdd (claimQubits V) (verifierWire (w:=work V) (Fin.natAdd V.proofQubits i)) := by
  apply Fin.ext
  change (if k V+i.val<k V then _ else _) = indexQubits V+clockWires V+(V.proofQubits+i.val)
  rw [if_neg (by omega)]
  dsimp only [k,Fin.natAdd,Fin.castAdd,Fin.last]
  try simp only [Fin.val_castLE]
  omega

lemma controls_flag (V : Verifier gatesG2) :
    zeroControls V (Fin.natAdd (k V) (Fin.last V.ancillaQubits)) =
      Fin.castAdd (claimQubits V) (flagWire (V:=V) (w:=work V)) := by
  apply Fin.ext
  change (if k V+V.ancillaQubits<k V then _ else _) =
    indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits)
  rw [if_neg (by omega)]
  dsimp only [k,Fin.natAdd,Fin.castAdd,Fin.last]
  try simp only [Fin.val_castLE]
  omega

/-- The literal readout controls exclude every arithmetic/history workspace bit. -/
theorem allZero_iff (V : Verifier gatesG2) (x : Basis (total V)) :
    (readoutLayout V).allZero x ↔ zeroZ V ((computationEquiv V (work V) x).1.1) := by
  rw [computationEquiv_body,decoded_zeroZ]
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i
      have hi := h (Fin.castAdd (V.ancillaQubits+1) i)
      simpa only [readoutLayout,readoutAndLayout,controls_index] using hi
    · intro j
      have hj := h (Fin.natAdd (k V) (Fin.castAdd 1 j))
      simpa only [readoutLayout,readoutAndLayout,controls_ancilla] using hj
    · have hf := h (Fin.natAdd (k V) (Fin.last V.ancillaQubits))
      simpa only [readoutLayout,readoutAndLayout,controls_flag] using hf
  · rintro ⟨hi,ha,hf⟩ j
    change x (zeroControls V j)=false
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j
    · rw [controls_index]
      exact hi i
    · refine Fin.lastCases ?_ (fun a=>?_) i
      · rw [controls_flag]
        exact hf
      · have he : a.castSucc=Fin.castAdd 1 a := Fin.ext rfl
        rw [he,controls_ancilla]
        exact ha a

/-- Compressing the actual physical acceptance flag along any correctly prepared coherent
certificate fiber gives precisely I minus the paper's rejection projector. -/
theorem readout_fiber_effect (V : Verifier gatesG2)
    (e : ComputationReg V → Basis (total V)) (he : Function.Injective e)
    (hbody : ∀q,(computationEquiv V (work V) (e q)).1.1=q.1)
    (hvalid : ∀q,e q (readoutLayout V).valid=decide (IsValidCertificate V q.2.2.1 q.2.2.2))
    (hclean : ∀q,(readoutLayout V).Clean (e q))
    (hz : ∀q,e q (readoutLayout V).zero=false)
    (ho : ∀q,e q (readoutLayout V).output=false) :
    (basisMatrix e)ᴴ*(circuitMatrix (readoutGates V))ᴴ*
      Matrix.diagonal (fun x : Basis (total V) => if x (readoutLayout V).output then (1:ℂ) else 0)*
        circuitMatrix (readoutGates V)*basisMatrix e = 1-rejectProjector V := by
  classical
  let a : ComputationReg V → Bool := fun q =>
    (decide (IsValidCertificate V q.2.2.1 q.2.2.2)) && !(decide (zeroZ V q.1))
  have hc : ∀y q,circuitMatrix (readoutGates V) y (e q)=
      if y=Function.update (e q) (readoutLayout V).output (a q) then 1 else 0 := by
    intro y q
    change circuitMatrix (readoutLayout V).gates y (e q)=_
    rw [(readoutLayout V).gates_matrix y (e q) (hclean q) (hz q),ho q,hvalid q]
    have hzero : (readoutLayout V).allZero (e q) ↔ zeroZ V q.1 := by
      rw [allZero_iff,hbody]
    simp only [hzero,Bool.false_xor]
    rfl
  calc
    _ = Matrix.diagonal (fun q=>if a q then (1:ℂ) else 0) :=
      flag_readout_compression e he (readoutLayout V).output a ho _ hc
    _ = 1-rejectProjector V := by
      rw [acceptProjector_diagonal]
      congr 1
      funext q
      by_cases hv : IsValidCertificate V q.2.2.1 q.2.2.2 <;> by_cases hz : zeroZ V q.1 <;>
        simp [a,hv,hz]

end QMAPerfectCompleteness.Main.CertificateReadoutEffect

end

/- Inline helpers retained from Solutions.CertificateVerifierEffect. -/
section


/-! From an actual initialized circuit transport to the exact published verifier effect. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
open BlockCircuit CertificateCoordinates CertificateVerifierLayout CertificateInitialization CoherentCertificate

variable (V : Verifier gatesG2) (w : ℕ)
variable (gs : List (Instr gatesG2 ((bodyWires V+w)+claimQubits V)))
variable (out : Fin ((bodyWires V+w)+claimQubits V))

lemma verifier_ancillaZero : (verifier V w gs out).ancillaZero =
    (basisMatrix (prepared V w)).submatrix (basisEquiv V w) (Equiv.refl (Basis (proofQubits V))) := by
  ext y p
  unfold Verifier.ancillaZero
  simp only [basisMatrix,Matrix.of_apply,Matrix.submatrix_apply,Equiv.coe_refl,id_eq]
  have he : basisEquiv V w y=prepared V w p ↔ y=(verifier V w gs out).initialState p := by
    change basisEquiv V w y=basisEquiv V w ((verifier V w gs out).initialState p) ↔ _
    exact (basisEquiv V w).injective.eq_iff
  by_cases h : y=(verifier V w gs out).initialState p <;> simp [h,he]
  rfl

lemma verifier_acceptProjector : (verifier V w gs out).acceptProjector =
    (Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)).submatrix
      (basisEquiv V w) (basisEquiv V w) := by
  ext y x
  by_cases h : y=x
  · subst x
    simp only [Verifier.acceptProjector,Matrix.diagonal_apply_eq,Matrix.submatrix_apply]
    rfl
  · simp [Verifier.acceptProjector,Matrix.diagonal_apply,h,(basisEquiv V w).injective.ne h]

/-- Exact matrix transport of initialized physical columns suffices for the complete verifier
acceptance equality; the proof explicitly transports both wire and proof coordinates. -/
theorem effect_of_initialized_transport
    (B : Matrix (Basis ((bodyWires V+w)+claimQubits V)) (CoherentCertificate.ProofReg V) ℂ)
    (hB : circuitMatrix gs * basisMatrix (prepared V w) =
      B.submatrix (Equiv.refl _) (proofEquiv V)) :
    (verifier V w gs out).acceptanceOperator =
      (Bᴴ * Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0) * B).submatrix
        (proofEquiv V) (proofEquiv V) := by
  have hinit : (verifier V w gs out).unitary * (verifier V w gs out).ancillaZero =
      B.submatrix (basisEquiv V w) (proofEquiv V) := by
    rw [verifier_unitary,verifier_ancillaZero,Matrix.submatrix_mul_equiv,hB]
    rfl
  have hreindex :
      (B.submatrix (basisEquiv V w) (proofEquiv V))ᴴ *
        (Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)).submatrix
          (basisEquiv V w) (basisEquiv V w) * B.submatrix (basisEquiv V w) (proofEquiv V) =
        (Bᴴ*Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)*B).submatrix
          (proofEquiv V) (proofEquiv V) := by
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  have hgram : (verifier V w gs out).acceptanceOperator =
      ((verifier V w gs out).unitary*(verifier V w gs out).ancillaZero)ᴴ *
        (verifier V w gs out).acceptProjector *
          ((verifier V w gs out).unitary*(verifier V w gs out).ancillaZero) := by
    simp only [Verifier.acceptanceOperator,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hgram,hinit,verifier_acceptProjector]
  exact hreindex

/-- The physical final flag, coherent unitary body, and η initialization give I minus exactly
the block-diagonal rejection effect used in the entangled-proof analysis. -/
theorem initialized_gram_of_readout
    (K : Matrix (Basis ((bodyWires V+w)+claimQubits V)) (ComputationReg V) ℂ)
    (R : Matrix (Basis ((bodyWires V+w)+claimQubits V)) (Basis ((bodyWires V+w)+claimQubits V)) ℂ)
    (U : CertificateMixture.Claim V → Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ)
    (hread : Kᴴ*Rᴴ*Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)*R*K =
      1-rejectProjector V)
    (hvalid : ∀c,IsValidCertificate V c.2.1 c.2.2 →
      U c=V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2)
    (hunitary : ∀c,(U c)ᴴ*U c=1) :
    let B := R*K*Matrix.blockDiagonal U*initialIsometry V
    Bᴴ*Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)*B =
      1-Matrix.blockDiagonal (CertificateMixture.claimRejection V) := by
  dsimp only
  have h := acceptance_effect_of_unitary_branches V U hvalid hunitary
  calc
    _ = (initialIsometry V)ᴴ*(Matrix.blockDiagonal U)ᴴ*
        (Kᴴ*Rᴴ*Matrix.diagonal (fun x : Basis ((bodyWires V+w)+claimQubits V) => if x out then (1:ℂ) else 0)*R*K)*
          Matrix.blockDiagonal U*initialIsometry V := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hread]; exact h

end QMAPerfectCompleteness.Main.CertificateVerifierEffect

end



/-! The complete literal coherent-certificate verifier. It initializes η, computes the
certificate-dependent arithmetic and validity, executes the exact dynamic block circuit,
and sets one physical accepting output iff the certificate is valid and Z is nonzero. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace QMAPerfectCompleteness.Main.CyclicVerifier
end QMAPerfectCompleteness.Main.CyclicVerifier
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CyclicVerifier
open BlockCircuit CertificateCoordinates CertificateMasterLayout CertificateVerifierLayout
open CoherentCertificate CertificatePreparation












lemma QMAPerfectCompleteness.Main.CyclicVerifier.prefix_transport (V : Verifier gatesG2) :
    circuitMatrix (prefixGates V)*basisMatrix (CertificateEtaTransport.rawEncoding V (work V)) = preparedEmbedding V := by
  have hr : CertificateEtaTransport.rawEncoding V (work V)=CertificatePreparation.rawEncoding V := rfl
  rw [hr]
  ext y p
  by_cases hy : y=prefixEncoding V p <;>
    simp [preparedEmbedding,basisMatrix,Matrix.mul_apply,mul_ite,CertificatePreparation.prefix_matrix,hy]

lemma QMAPerfectCompleteness.Main.CyclicVerifier.block_transport (V : Verifier gatesG2) :
    circuitMatrix (CertificateBlockCorrectness.gates V)*preparedEmbedding V = preparedEmbedding V*bodyMatrix V := by
  exact CertificateBlockCorrectness.actual_coherent_block_transports V

lemma QMAPerfectCompleteness.Main.CyclicVerifier.mul_column_reindex {α β γ δ : Type*} [Fintype β]
    (A : Matrix α β ℂ) (B : Matrix β γ ℂ) (f : δ → γ) :
    A*B.submatrix (Equiv.refl β) f = (A*B).submatrix (Equiv.refl α) f := by
  simpa only [Equiv.coe_refl,Matrix.submatrix_id_id] using
    Matrix.submatrix_mul_equiv A B (Equiv.refl α) (Equiv.refl β) f



/-- All actual initialized circuit columns, with exact physical and proof-coordinate transport. -/
theorem QMAPerfectCompleteness.Main.CyclicVerifier.initialized_transport (V : Verifier gatesG2) :
    circuitMatrix (gates V)*basisMatrix (prepared V (work V)) =
      (initializedMatrix V).submatrix (Equiv.refl _) (proofEquiv V) := by
  simp only [gates,BlockProof.circuitMatrix_append,Matrix.mul_assoc]
  rw [CertificateEtaTransport.eta_transport]
  simp only [mul_column_reindex]
  have hi : circuitMatrix (readoutGates V)*
      (circuitMatrix (CertificateBlockCorrectness.gates V)*
        (circuitMatrix (prefixGates V)*(basisMatrix (CertificateEtaTransport.rawEncoding V (work V))*initialIsometry V))) =
      initializedMatrix V := by
    rw [← Matrix.mul_assoc _ _ (initialIsometry V),prefix_transport,
      ← Matrix.mul_assoc _ _ (initialIsometry V),block_transport]
    simp only [initializedMatrix,Matrix.mul_assoc]
  rw [hi]

lemma QMAPerfectCompleteness.Main.CyclicVerifier.body_unitary (V : Verifier gatesG2) : (bodyMatrix V)ᴴ*bodyMatrix V=1 := by
  have hK : (preparedEmbedding V)ᴴ*preparedEmbedding V=1 := by
    have h := basis_diagonal_compression (prefixEncoding V) (prefix_injective V) (fun _=> (1:ℂ))
    simpa [preparedEmbedding,Function.comp_def] using h
  have hC : (circuitMatrix (CertificateBlockCorrectness.gates V))ᴴ*circuitMatrix (CertificateBlockCorrectness.gates V)=1 :=
    Matrix.mem_unitaryGroup_iff'.mp (CircuitProof.circuit_unitary _)
  exact gram_of_transport _ _ _ _ hC hK hK (block_transport V)

lemma QMAPerfectCompleteness.Main.CyclicVerifier.body_branch_unitary (V : Verifier gatesG2) (c : CertificateMixture.Claim V) :
    (V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2)ᴴ*
      V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2=1 := by
  have h := body_unitary V
  rw [bodyMatrix,Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul] at h
  ext y x
  have he := congrArg (fun M : Matrix (Logical V) (Logical V) ℂ => M (y,c) (x,c)) h
  simpa [Matrix.blockDiagonal_apply,Matrix.one_apply,Prod.mk.injEq] using he

lemma QMAPerfectCompleteness.Main.CyclicVerifier.readout_effect (V : Verifier gatesG2) :
    (preparedEmbedding V)ᴴ*(circuitMatrix (readoutGates V))ᴴ*
      Matrix.diagonal (fun x : QMAPerfectCompleteness.Main.CyclicVerifier.Physical V => if x (readoutLayout V).output then (1:ℂ) else 0)*
        circuitMatrix (readoutGates V)*preparedEmbedding V=1-rejectProjector V := by
  apply CertificateReadoutEffect.readout_fiber_effect V (prefixEncoding V) (prefix_injective V)
  · intro q
    exact congrArg Prod.fst (prefix_logical V q)
  · intro q
    rw [readout_valid]
    by_cases hv : IsValidCertificate V q.2.2.1 q.2.2.2 <;> simpa [hv] using prefix_valid V q
  · intro q j
    exact prefix_readout_flags V q ((finCongr (show zeroBits V+1=readoutWork V by
      dsimp [zeroBits,readoutWork,k]; omega)) j)
  · intro q
    rw [readout_zero]
    exact prefix_readout_tags V q 0
  · intro q
    rw [readout_output]
    exact prefix_readout_tags V q 1

/-- Exact acceptance operator of the actual coherent-certificate gate-list verifier. -/
theorem solution (V : Verifier gatesG2) :
    (compileVerifier V).acceptanceOperator =
      (1-Matrix.blockDiagonal (CertificateMixture.claimRejection V)).submatrix (proofEquiv V) (proofEquiv V) := by
  have hgram := CertificateVerifierEffect.initialized_gram_of_readout V (work V) (readoutLayout V).output
    (preparedEmbedding V) (circuitMatrix (readoutGates V))
    (fun c : CertificateMixture.Claim V => V.blockUnitary (indexQubits V) c.1 c.2.1 c.2.2)
    (readout_effect V) (fun _ _=>rfl) (body_branch_unitary V)
  have hE := CertificateVerifierEffect.effect_of_initialized_transport V (work V) (gates V) (readoutLayout V).output
    (initializedMatrix V) (initialized_transport V)
  change (compileVerifier V).acceptanceOperator = _ at hE
  rw [show (initializedMatrix V)ᴴ*
      Matrix.diagonal (fun x : QMAPerfectCompleteness.Main.CyclicVerifier.Physical V => if x (readoutLayout V).output then (1:ℂ) else 0)*initializedMatrix V=
      1-Matrix.blockDiagonal (CertificateMixture.claimRejection V) from hgram] at hE
  exact hE
