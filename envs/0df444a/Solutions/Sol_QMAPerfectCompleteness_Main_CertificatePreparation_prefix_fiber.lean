-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificatePreparation.prefix_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:47:45.101348+00:00
-- url     : https://prove2.me/submissions/176e734e-e1a8-4ccb-b0f2-72006cfdc766

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
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificatePreparation_logical_eq_of_data
import Theorems.Thm_QMAPerfectCompleteness_Main_CertificatePreparation_prep_logical
import Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_values

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
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits

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













/-- Prepared threshold bits depend only on the certificate, even when all quantum body bits
change. Other wires retain their own original value. -/
theorem state_agrees_at (x y : Basis n) (hx : L.Clean x) (hy : L.Clean y)
    (hcert : ∀ d j, x (L.wire (.certificate d j)) = y (L.wire (.certificate d j)))
    (w : Fin n) (hframe : (∀ d j, w ≠ L.wire (.word d j)) → x w=y w) :
    L.state x w = L.state y w := by
  classical
  by_cases hr : ∃ d j, w=L.wire (.word d j)
  · obtain ⟨d,j,rfl⟩ := hr
    have hv (d : Fin 2) : L.value x d = L.value y d :=
      congrArg littleValue (funext (hcert d))
    have hword : (fun j => L.state x (L.wire (.word d j))) =
        (fun j => L.state y (L.wire (.word d j))) := by
      apply ClockCircuits.littleValue_injective
      rw [L.values x hx d,L.values y hy d,hv 0,hv 1]
    exact congrFun hword j
  · have hn : ∀ d j, w ≠ L.wire (.word d j) := by simpa only [not_exists] using hr
    rw [L.state_outside x w hn,L.state_outside y w hn,hframe hn]

end Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation

end

/- Inline helpers retained from Solutions.CertificateThresholdLayout. -/
section


/-! The actual master-layout placement of the coherent binary threshold preparation. -/
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open ThresholdPreparation









@[simp] theorem thresholdWire_certificate (V : Verifier gatesG2) (s : Fin 2) (j : Fin (k V)) :
    thresholdWire V (.certificate s j) = certificate V s j := rfl
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

/-- Equal logical certificates give identical reads at every physical certificate wire. -/
lemma claim_agrees (x y : Physical V) (h : (coords V x).1.2=(coords V y).1.2)
    (w : Fin (total V)) (hw : bodyWires V+work V ≤ w.val) : x w=y w := by
  have hr : (fun i => x (Fin.natAdd (bodyWires V+work V) i)) =
      (fun i => y (Fin.natAdd (bodyWires V+work V) i)) := by
    apply (claimEquiv V).injective
    exact h
  let i : Fin (claimQubits V) := ⟨w.val-(bodyWires V+work V),by have := w.isLt; dsimp [total] at this; omega⟩
  have he : Fin.natAdd (bodyWires V+work V) i=w := Fin.ext (by dsimp [i]; omega)
  simpa only [he] using congrFun hr i


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






/-- The arithmetic workspace is a function of the retained certificate alone. -/
theorem prep_fiber (p : Logical V) :
    coords V (prepState V (rawEncoding V p)) = (p,prepWorkspace V p.2) := by
  apply Prod.ext
  · rw [prep_logical,coords_raw]
  · funext i
    change prepState V (rawEncoding V p) (workWire V i) =
      prepState V (rawEncoding V (dummyBody V,p.2)) (workWire V i)
    apply (thresholdLayout V).state_agrees_at _ _ (raw_clean V p) (raw_clean V (dummyBody V,p.2))
    · intro d j
      rw [thresholdLayout_wire,thresholdWire_certificate]
      apply claim_agrees V
      · rw [coords_raw,coords_raw]
      · change bodyWires V+work V ≤ bodyWires V+work V+V.proofQubits+(finProdFinEquiv (d,j)).val
        omega
    · intro _
      rw [raw_work,raw_work]



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



lemma QMAPerfectCompleteness.Main.CertificatePreparation.validity_work (t : Fin 6) :
    bodyWires V ≤ (validity V t).val ∧ (validity V t).val < bodyWires V+work V := by
  have ht := t.isLt
  change bodyWires V ≤ bodyWires V+(oldWork V+prepWork V+2)+t.val ∧ _
  change _ ∧ bodyWires V+(oldWork V+prepWork V+2)+t.val < bodyWires V+work V
  dsimp only [work]
  omega

lemma QMAPerfectCompleteness.Main.CertificatePreparation.data_ne_validity (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) (t : Fin 6) : w ≠ validity V t := by
  intro h
  have ht := validity_work V t
  have hv := congrArg Fin.val h
  omega

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_validity (p : Logical V) (t : Fin 6) : prepState V (rawEncoding V p) (validity V t)=false := by
  apply prep_at_work V p _ (validity_work V t).1 (validity_work V t).2
  intro d j
  exact validity_ne_word V t d j







lemma QMAPerfectCompleteness.Main.CertificatePreparation.raw_a (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 0=p.2.2.1.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 0 j)) = _
  rw [CertificateClaimBits.a_value,coords_raw]
lemma QMAPerfectCompleteness.Main.CertificatePreparation.raw_b (p : Logical V) : (thresholdLayout V).value (rawEncoding V p) 1=p.2.2.2.val := by
  change ComparisonCircuits.littleValue (fun j => rawEncoding V p (certificate V 1 j)) = _
  rw [CertificateClaimBits.b_value,coords_raw]

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_values (p : Logical V) (d : Fin 6) :
    littleValue (fun j => prepState V (rawEncoding V p) (prepWord V d j)) =
      (![p.2.2.1.val,2*p.2.2.1.val,p.2.2.2.val,2*p.2.2.2.val,
        3*p.2.2.1.val,3*p.2.2.1.val+p.2.2.2.val] : Fin 6 → ℕ) d := by
  have h := (thresholdLayout V).values (rawEncoding V p) (raw_clean V p) d
  rw [raw_a,raw_b] at h
  simpa only [prepState,thresholdLayout_wire,thresholdWire_word] using h

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_aValue (p : Logical V) :
    (CertificateValidityCircuit.layout V).aValue (prepState V (rawEncoding V p)) = p.2.2.1.val := by
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 0 j)) = _
  simpa using prep_values V p 0
lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_bValue (p : Logical V) :
    (CertificateValidityCircuit.layout V).bValue (prepState V (rawEncoding V p)) = p.2.2.2.val := by
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 2 j)) = _
  simpa using prep_values V p 2

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_cmp_left (p : Logical V) :
    littleValue ((prepState V (rawEncoding V p)) ∘ VariableComparison.leftWire (CertificateValidityCircuit.layout V).cmp) = p.2.2.1.val := by
  simp only [Function.comp_def,show (CertificateValidityCircuit.layout V).cmp = (comparatorWires V).comparator 0 from rfl]
  simp_rw [DynamicBlockCompiler.RangeWires.comparator_left]
  exact prep_aValue V p

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_cmp_right (p : Logical V) :
    littleValue ((prepState V (rawEncoding V p)) ∘ VariableComparison.rightWire (CertificateValidityCircuit.layout V).cmp) = 2*p.2.2.2.val := by
  simp only [Function.comp_def,show (CertificateValidityCircuit.layout V).cmp = (comparatorWires V).comparator 0 from rfl]
  simp_rw [DynamicBlockCompiler.RangeWires.comparator_right]
  change littleValue (fun j => prepState V (rawEncoding V p) (prepWord V 3 j)) = _
  simpa using prep_values V p 3

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prep_truth (p : Logical V) :
    (CertificateValidityCircuit.layout V).truth (prepState V (rawEncoding V p)) =
      CertificateValidity.checks (k V) p.2.2.1.val p.2.2.2.val := by
  unfold CertificateValidity.Layout.truth CertificateValidity.checks VariableEquality.comparisonBit
  rw [prep_aValue,prep_bValue,prep_cmp_left,prep_cmp_right]



lemma QMAPerfectCompleteness.Main.CertificatePreparation.prefix_data (p : Logical V) (w : Fin (total V))
    (hw : w.val<bodyWires V ∨ bodyWires V+work V ≤ w.val) : prefixEncoding V p w=rawEncoding V p w := by
  rw [prefixEncoding,Function.update_of_ne (data_ne_validity V w hw 5)]
  rw [CertificateValidity.Layout.action_outside_tags]
  · exact prep_data V _ _ hw
  · intro t
    exact data_ne_validity V w hw ⟨t.val,by have := t.isLt; omega⟩

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prefix_logical (p : Logical V) : (coords V (prefixEncoding V p)).1=p := by
  rw [logical_eq_of_data V _ (rawEncoding V p) (prefix_data V p),coords_raw]

lemma QMAPerfectCompleteness.Main.CertificatePreparation.prefix_valid (p : Logical V) : prefixEncoding V p (validity V 5) =
    decide (IsValidCertificate V p.2.2.1.val p.2.2.2.val) := by
  simp only [prefixEncoding,Function.update_self]



/-- The full actual prefix leaves a workspace determined by the certificate alone. -/
theorem solution (p : Logical V) :
    coords V (prefixEncoding V p) = (p,prefixWorkspace V p.2) := by
  apply Prod.ext
  · exact prefix_logical V p
  · funext i
    let w := workWire V i
    change prefixEncoding V p w = prefixEncoding V (dummyBody V,p.2) w
    by_cases ho : w=validity V 5
    · rw [ho,prefix_valid,prefix_valid]
    · rw [prefixEncoding,prefixEncoding,Function.update_of_ne ho,Function.update_of_ne ho]
      by_cases hc : ∃ t : Fin 5, w=(CertificateValidityCircuit.layout V).tags t
      · obtain ⟨t,ht⟩ := hc
        rw [ht]
        rw [CertificateValidity.Layout.action_tags,CertificateValidity.Layout.action_tags,prep_truth,prep_truth]
        · intro t
          exact prep_validity V _ ⟨t.val,by have := t.isLt; omega⟩
        · intro t
          exact prep_validity V _ ⟨t.val,by have := t.isLt; omega⟩
      · have hn : ∀ t : Fin 5, w ≠ (CertificateValidityCircuit.layout V).tags t := by simpa only [not_exists] using hc
        rw [CertificateValidity.Layout.action_outside_tags _ _ _ hn,
          CertificateValidity.Layout.action_outside_tags _ _ _ hn]
        have h1 := congrFun (congrArg Prod.snd (prep_fiber V p)) i
        have h2 := congrFun (congrArg Prod.snd (prep_fiber V (dummyBody V,p.2))) i
        exact h1.trans h2.symm
