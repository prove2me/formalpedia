-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificatePreparation.prep_logical
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:51:00.645207+00:00
-- url     : https://prove2.me/submissions/45519d47-0b8c-492f-8c2e-2463f70c5f03

/- Generated from Solutions.CertificatePreparation by authoritative Stage-2 skeleton subtraction.
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



end QMAPerfectCompleteness.Main.CertificateMasterLayout

end



/-! Actual threshold preparation on the physical coherent verifier, with a certificate-only
workspace fiber. The arithmetic garbage may be retained throughout the quantum block. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CertificatePreparation
end QMAPerfectCompleteness.Main.CertificatePreparation
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificatePreparation
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateMasterLayout ThresholdPreparation
open ComparisonCircuits
variable (V : Verifier gatesG2)



















@[simp] lemma QMAPerfectCompleteness.Main.CertificatePreparation.thresholdLayout_wire : (thresholdLayout V).wire = thresholdWire V := rfl




lemma QMAPerfectCompleteness.Main.CertificatePreparation.word_work (d : Fin 6) (j : Fin (r V)) :
    bodyWires V ≤ (prepWord V d j).val ∧ (prepWord V d j).val < bodyWires V+work V := by
  have h := CertificateRangeCircuit.word_bounds V d j
  have hm : oldWork V+6*r V ≤ work V := by dsimp only [work,prepWork,r,k]; omega
  dsimp only [r,k] at h hm ⊢
  omega









lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_data (x : Physical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prepState V x w=x w := by
  apply (thresholdLayout V).state_outside
  intro d j h
  rw [thresholdLayout_wire,thresholdWire_word] at h
  have hh := congrArg Fin.val h
  have hb := word_work V d j
  omega

/-- Logical data and the certificate are untouched by the arithmetic prefix. -/
theorem solution (x : Physical V) : (coords V (prepState V x)).1=(coords V x).1 := by
  apply Prod.ext
  · rw [computationEquiv_body,computationEquiv_body]
    change decode (fun i => prepState V x (Fin.castAdd (claimQubits V) i)) =
      decode (fun i => x (Fin.castAdd (claimQubits V) i))
    apply Prod.ext
    · change Fin.ofNat (2^indexQubits V)
        (bitsValue (fun i => prepState V x (Fin.castAdd (claimQubits V) i)) indexWire) =
        Fin.ofNat (2^indexQubits V) (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) indexWire)
      congr 1
      unfold bitsValue
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply congrArg (fun b : Bool => b=true)
      apply prep_data V x
      left
      have hi := i.isLt
      change i.val < bodyWires V
      dsimp [bodyWires]
      omega
    · apply Prod.ext
      · change Fin.ofNat (ell V.proofQubits+1)
          (bitsValue (fun i => prepState V x (Fin.castAdd (claimQubits V) i)) clockWire) =
          Fin.ofNat (ell V.proofQubits+1) (bitsValue (fun i => x (Fin.castAdd (claimQubits V) i)) clockWire)
        congr 1
        unfold bitsValue
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        apply congrArg (fun b : Bool => b=true)
        apply prep_data V x
        left
        have hi := i.isLt
        change indexQubits V+i.val < bodyWires V
        dsimp [bodyWires]
        omega
      · apply Prod.ext
        · funext i
          apply prep_data V x
          left
          have hi := i.isLt
          change indexQubits V+clockWires V+i.val < bodyWires V
          dsimp [bodyWires]
          omega
        · apply prep_data V x
          left
          change indexQubits V+clockWires V+(V.proofQubits+V.ancillaQubits) < bodyWires V
          dsimp [bodyWires]
          omega
  · rw [computationEquiv_claim,computationEquiv_claim]
    congr 1
    funext i
    apply prep_data V x
    right
    change bodyWires V+work V ≤ bodyWires V+work V+i.val
    omega
