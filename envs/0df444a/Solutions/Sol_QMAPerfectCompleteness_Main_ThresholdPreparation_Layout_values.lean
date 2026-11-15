-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.values
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:57:44.748205+00:00
-- url     : https://prove2.me/submissions/d9a4b051-034b-4b51-af1f-2d2a07904f74

/- Generated from Solutions.ThresholdPreparation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_copies_odd_word
import Theorems.Thm_QMAPerfectCompleteness_Main_VariableAddition_Layout_commands_output

/- Inline helpers retained from Solutions.ClockCircuits. -/
section


/-! Controlled cyclic increment of a little-endian binary clock, using reusable clean flags. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ClockCircuits
open ReversibleGadgets ControlCircuits ComparisonCircuits

variable {r n : ℕ} (L : AndLayout (r+1) n)



















































theorem littleValue_getLsbD {k : ℕ} (v : BitVec k) :
    littleValue (fun j : Fin k => v.getLsbD j) = v.toNat := by
  change littleValue (fun j : Fin k => v.toNat.testBit j) = v.toNat
  rw [littleValue_testBit, Nat.mod_eq_of_lt v.isLt]









end QMAPerfectCompleteness.Main.ClockCircuits

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





/-- The clean output register stores the sum modulo its declared binary width. -/
theorem commands_value (x : Basis n) (hcarry : ∀ j, x (L.carry j) = false)
    (hp : x L.temp = false) (hout : ∀ j, x (L.output j) = false) :
    littleValue (fun j => eval L.commands x (L.output j)) =
      (littleValue (fun j => x (L.left j)) + littleValue (fun j => x (L.right j))) % 2^r := by
  simp_rw [L.commands_output x hcarry hp,hout,Bool.false_xor]
  rw [littleValue_getLsbD,BitVec.toNat_add]
  rfl

@[simp] theorem commands_carry (x : Basis n) (j : Fin (r+1)) :
    eval L.commands x (L.carry j) = x (L.carry j) :=
  L.commands_frame x _ (fun i => (L.output_ne_carry i j).symm)

@[simp] theorem commands_temp (x : Basis n) : eval L.commands x L.temp = x L.temp :=
  L.commands_frame x _ (fun i => L.temp_ne_output i)

end Layout
end QMAPerfectCompleteness.Main.VariableAddition

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



/-- Copying each selected source once XORs it into its target, with every other wire fixed. -/
theorem eval_target (js : List ι) (hjs : js.Nodup) (x : Basis n) (j : ι) :
    eval (commands source target hd js) x (target j) =
      if j ∈ js then xor (x (target j)) (x (source j)) else x (target j) := by
  induction js generalizing x j with
  | nil => simp [commands,eval]
  | cons i js ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hjs
    change eval (commands source target hd js)
      (Function.update x (target i) (xor (x (target i)) (x (source i)))) (target j) = _
    rw [ih hn]
    simp only [Function.update_of_ne (hd j i)]
    by_cases he : j=i
    · subst j; simp [hi]
    · have ht : target j ≠ target i := target.injective.ne he
      simp [he,ht]



end QMAPerfectCompleteness.Main.RegisterCopies

end



/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
end QMAPerfectCompleteness.Main.ThresholdPreparation
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits





namespace QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
variable {k n : ℕ} (L : Layout k n)

















lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copyIndices_nodup : (copyIndices (k := k)).Nodup :=
  (List.nodup_finRange _).map finProdFinEquiv.symm.injective

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.mem_copyIndices (i : CopyIndex (k := k)) : i ∈ copyIndices := by
  apply List.mem_map.mpr
  exact ⟨finProdFinEquiv i,by simp,finProdFinEquiv.symm_apply_apply i⟩







theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_target (x : Basis n) (i : CopyIndex (k := k)) :
    L.copyState x (L.target i) = xor (x (L.target i)) (x (L.source i)) := by
  have h := RegisterCopies.eval_target L.source L.targetEmbedding L.source_ne_target
    copyIndices copyIndices_nodup x i
  simp only [mem_copyIndices,if_true] at h
  change L.copyState x (L.target i) = xor (x (L.target i)) (x (L.source i)) at h
  exact h

theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_outside (x : Basis n) (w : Fin n) (hw : ∀ i, w ≠ L.target i) :
    L.copyState x w = x w :=
  RegisterCopies.eval_outside L.source L.targetEmbedding L.source_ne_target _ x w (fun i _ => hw i)



@[simp] theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_carry (x : Basis n) (j : Fin (k+3)) :
    L.copyState x (L.wire (.carry j)) = x (L.wire (.carry j)) := by
  apply L.copies_outside
  intro i h
  have hh := L.wire.injective h
  cases hh

@[simp] theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_temp (x : Basis n) : L.copyState x (L.wire .temp) = x (L.wire .temp) := by
  apply L.copies_outside
  intro i h
  have hh := L.wire.injective h
  cases hh

/-- A target word bit that is outside the selected copy positions is untouched. -/
lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_word_outside (x : Basis n) (d : Fin 6) (j : Fin (k+2))
    (hn : ∀ i : CopyIndex (k := k), d.val=i.1.val → j.val ≠ i.2.val+i.1.val%2) :
    L.copyState x (L.wire (.word d j)) = x (L.wire (.word d j)) := by
  apply L.copies_outside
  intro i h
  have hp := L.wire.injective h
  obtain ⟨hd,hj⟩ := Slot.word.inj hp
  have hdv := congrArg Fin.val hd
  have hjv := congrArg Fin.val hj
  exact hn i hdv hjv

lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.target_even (d : Fin 4) (hd : d.val%2=0) (j : Fin k) :
    L.target (d,j) = L.wire (.word ⟨d.val,by have := d.isLt; omega⟩ (Fin.castAdd 2 j)) := by
  unfold target
  congr 2
  apply Fin.ext
  exact Nat.add_zero j.val ▸ congrArg (fun v => j.val+v) hd



/-- Even-numbered word copies are zero-extended without altering the certificate. -/
theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_even_word (x : Basis n) (hz : ∀ d j, x (L.wire (.word d j)) = false)
    (d : Fin 4) (hd : d.val%2=0) :
    (fun j => L.copyState x (L.wire (.word ⟨d.val,by have := d.isLt; omega⟩ j))) =
      Fin.append (fun j => x (L.source (d,j))) (fun _ : Fin 2 => false) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [← L.target_even d hd j,L.copies_target]
    simp only [target,hz,Bool.false_xor,Fin.append_left]
  · rw [Fin.append_right]
    rw [L.copies_word_outside]
    · exact hz _ _
    · rintro ⟨e,i⟩ he hpos
      have heq : e=d := Fin.ext he.symm
      subst e
      simp only [Fin.val_natAdd,hd,Nat.add_zero] at hpos
      have hi := i.isLt
      omega



lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.littleValue_append_zero {a b : ℕ} (x : Basis a) :
    littleValue (Fin.append x (fun _ : Fin b => false)) = littleValue x := by
  simp only [littleValue,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp

lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.littleValue_cons_false {a : ℕ} (x : Basis a) :
    littleValue (Fin.cons false x) = 2*littleValue x := by
  simp only [littleValue,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.val_succ,Bool.false_eq_true,if_false,zero_add]
  simp only [pow_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases h : x j <;> simp [h,Nat.mul_comm]

/-- The four initial words have exactly values a,2a,b,2b. -/
theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_values (x : Basis n) (hz : ∀ d j, x (L.wire (.word d j)) = false) :
    littleValue (fun j => L.copyState x (L.wire (.word 0 j))) =
      littleValue (fun j => x (L.wire (.certificate 0 j))) ∧
    littleValue (fun j => L.copyState x (L.wire (.word 1 j))) =
      2*littleValue (fun j => x (L.wire (.certificate 0 j))) ∧
    littleValue (fun j => L.copyState x (L.wire (.word 2 j))) =
      littleValue (fun j => x (L.wire (.certificate 1 j))) ∧
    littleValue (fun j => L.copyState x (L.wire (.word 3 j))) =
      2*littleValue (fun j => x (L.wire (.certificate 1 j))) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [littleValue_append_zero,source] using
      congrArg littleValue (L.copies_even_word x hz 0 (by decide))
  · simpa [littleValue_cons_false,littleValue_append_zero,source] using
      congrArg littleValue (L.copies_odd_word x hz 1 (by decide))
  · simpa [littleValue_append_zero,source] using
      congrArg littleValue (L.copies_even_word x hz 2 (by decide))
  · simpa [littleValue_cons_false,littleValue_append_zero,source] using
      congrArg littleValue (L.copies_odd_word x hz 3 (by decide))










lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.three_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 4 j)) :
    eval L.three.commands x w = x w := by
  apply L.three.commands_frame
  intro j
  rw [L.three_output]
  exact hw j

lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.upper_outside (x : Basis n) (w : Fin n) (hw : ∀ j, w ≠ L.wire (.word 5 j)) :
    eval L.upper.commands x w = x w := by
  apply L.upper.commands_frame
  intro j
  rw [L.upper_output]
  exact hw j

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.three_word (x : Basis n) (d : Fin 6) (hd : d ≠ 4) (j : Fin (k+2)) :
    eval L.three.commands x (L.wire (.word d j)) = x (L.wire (.word d j)) := by
  apply L.three_outside
  intro i h
  exact hd (Slot.word.inj (L.wire.injective h)).1

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.upper_word (x : Basis n) (d : Fin 6) (hd : d ≠ 5) (j : Fin (k+2)) :
    eval L.upper.commands x (L.wire (.word d j)) = x (L.wire (.word d j)) := by
  apply L.upper_outside
  intro i h
  exact hd (Slot.word.inj (L.wire.injective h)).1

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.three_carry_state (x : Basis n) (j : Fin (k+3)) :
    eval L.three.commands x (L.wire (.carry j)) = x (L.wire (.carry j)) := by
  rw [← L.three_carry,VariableAddition.Layout.commands_carry]

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.three_temp_state (x : Basis n) : eval L.three.commands x (L.wire .temp) = x (L.wire .temp) := by
  rw [← L.three_temp,VariableAddition.Layout.commands_temp]

lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_high_word (x : Basis n) (d : Fin 6) (hd : 4 ≤ d.val) (j : Fin (k+2)) :
    L.copyState x (L.wire (.word d j)) = x (L.wire (.word d j)) := by
  apply L.copies_word_outside
  intro i he
  have hi := i.1.isLt
  omega



lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.state_eq (x : Basis n) : L.state x =
    eval L.upper.commands (eval L.three.commands (L.copyState x)) := by
  rw [state,commands,VariableAddition.eval_append,VariableAddition.eval_append]
  rfl









lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.three_value (x : Basis n) (hx : L.Clean x) :
    littleValue (fun j => eval L.three.commands (L.copyState x) (L.wire (.word 4 j))) = 3*L.value x 0 := by
  obtain ⟨hz,hcarry,hp⟩ := hx
  have hc : ∀ j, L.copyState x (L.three.carry j) = false := by intro j; rw [L.three_carry,L.copies_carry,hcarry]
  have ht : L.copyState x L.three.temp = false := by rw [L.three_temp,L.copies_temp,hp]
  have ho : ∀ j, L.copyState x (L.three.output j) = false := by
    intro j; rw [L.three_output,L.copies_high_word x 4 (by decide),hz]
  have h := L.three.commands_value (L.copyState x) hc ht ho
  simp only [L.three_output,L.three_left,L.three_right] at h
  obtain ⟨ha,h2a,_,_⟩ := L.copies_values x hz
  rw [ha,h2a] at h
  have hb := littleValue_lt_two_pow (fun j => x (L.wire (.certificate 0 j)))
  have hpw : 2^(k+2) = 4*2^k := by simp [pow_add,Nat.mul_comm]
  have hbound : L.value x 0 + 2*L.value x 0 < 2^(k+2) := by
    unfold value
    rw [hpw]
    omega
  simp only [value] at hbound h ⊢
  rw [Nat.mod_eq_of_lt hbound] at h
  omega

lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.upper_value (x : Basis n) (hx : L.Clean x) :
    littleValue (fun j => L.state x (L.wire (.word 5 j))) = 3*L.value x 0 + L.value x 1 := by
  obtain ⟨hz,hcarry,hp⟩ := hx
  have hc : ∀ j, eval L.three.commands (L.copyState x) (L.upper.carry j) = false := by
    intro j; rw [L.upper_carry,L.three_carry_state,L.copies_carry,hcarry]
  have ht : eval L.three.commands (L.copyState x) L.upper.temp = false := by
    rw [L.upper_temp,L.three_temp_state,L.copies_temp,hp]
  have ho : ∀ j, eval L.three.commands (L.copyState x) (L.upper.output j) = false := by
    intro j; rw [L.upper_output,L.three_word _ 5 (by decide),L.copies_high_word x 5 (by decide),hz]
  have h := L.upper.commands_value (eval L.three.commands (L.copyState x)) hc ht ho
  simp only [L.upper_output,L.upper_left,L.upper_right,L.three_word _ 2 (by decide)] at h
  obtain ⟨_,_,hb,_⟩ := L.copies_values x hz
  rw [L.three_value x ⟨hz,hcarry,hp⟩,hb] at h
  have haBound := littleValue_lt_two_pow (fun j => x (L.wire (.certificate 0 j)))
  have hbBound := littleValue_lt_two_pow (fun j => x (L.wire (.certificate 1 j)))
  have hpw : 2^(k+2) = 4*2^k := by simp [pow_add,Nat.mul_comm]
  have hbound : 3*L.value x 0 + L.value x 1 < 2^(k+2) := by unfold value; rw [hpw]; omega
  simp only [value] at hbound h ⊢
  rw [Nat.mod_eq_of_lt hbound] at h
  simpa only [state_eq] using h

/-- Exact dynamic thresholds needed by SELECT, without enumeration of certificates. -/
theorem solution (x : Basis n) (hx : L.Clean x) :
    ∀ d : Fin 6, littleValue (fun j => L.state x (L.wire (.word d j))) =
      (![L.value x 0,2*L.value x 0,L.value x 1,2*L.value x 1,
        3*L.value x 0,3*L.value x 0+L.value x 1] : Fin 6 → ℕ) d := by
  obtain ⟨ha,h2a,hb,h2b⟩ := L.copies_values x hx.1
  intro d
  fin_cases d
  · change littleValue (fun j => L.state x (L.wire (.word 0 j))) = L.value x 0
    rw [state_eq]
    simp_rw [L.upper_word _ 0 (by decide),L.three_word _ 0 (by decide)]
    exact ha
  · change littleValue (fun j => L.state x (L.wire (.word 1 j))) = 2*L.value x 0
    rw [state_eq]
    simp_rw [L.upper_word _ 1 (by decide),L.three_word _ 1 (by decide)]
    exact h2a
  · change littleValue (fun j => L.state x (L.wire (.word 2 j))) = L.value x 1
    rw [state_eq]
    simp_rw [L.upper_word _ 2 (by decide),L.three_word _ 2 (by decide)]
    exact hb
  · change littleValue (fun j => L.state x (L.wire (.word 3 j))) = 2*L.value x 1
    rw [state_eq]
    simp_rw [L.upper_word _ 3 (by decide),L.three_word _ 3 (by decide)]
    exact h2b
  · change littleValue (fun j => L.state x (L.wire (.word 4 j))) = 3*L.value x 0
    rw [state_eq]
    simp_rw [L.upper_word _ 4 (by decide)]
    exact L.three_value x hx
  · exact L.upper_value x hx
