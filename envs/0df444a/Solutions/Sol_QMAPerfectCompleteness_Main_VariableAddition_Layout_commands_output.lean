-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.VariableAddition.Layout.commands_output
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:55:53.019781+00:00
-- url     : https://prove2.me/submissions/0d800af3-c814-4fe6-8bd6-57a1ce6f6249

/- Generated from Solutions.VariableAddition by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Theorems.Thm_QMAPerfectCompleteness_Main_VariableAddition_Layout_carryPrefix_carry

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













end QMAPerfectCompleteness.Main.BooleanCircuits

end



/-! Literal variable-register addition using a ripple carry, copied sums, and uncomputation. -/
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.VariableAddition
end QMAPerfectCompleteness.Main.VariableAddition
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.VariableAddition
open BooleanCircuits ComparisonCircuits ClockCircuits







set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem QMAPerfectCompleteness.Main.VariableAddition.carryCommands_eval {n : ℕ} (e : Fin 5 ↪ Fin n) (x : Basis n) :
    eval (carryCommands e) x = Function.update x (e 3)
      (xor (x (e 3)) (xor (x (e 0) && x (e 1))
        ((xor (x (e 4)) (xor (x (e 0)) (x (e 1)))) && x (e 2)))) := by
  funext w
  by_cases h0 : w=e 0
  · subst w
    simp [carryCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff]
  · by_cases h1 : w=e 1
    · subst w
      simp [carryCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff]
    · by_cases h3 : w=e 3
      · subst w
        cases ha : x (e 0) <;> cases hb : x (e 1) <;> cases hc : x (e 2) <;>
          cases hp : x (e 4) <;> cases hd : x (e 3) <;>
          simp [carryCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,ha,hb,hc,hp,hd]
      · by_cases h4 : w=e 4
        · subst w
          simp [carryCommands,eval,evalCommand,Function.update_apply,e.injective.eq_iff,Bool.xor_assoc]
        · simp [carryCommands,eval,evalCommand,Function.update_apply,h0,h1,h3,h4]



lemma QMAPerfectCompleteness.Main.VariableAddition.eval_append {n : ℕ} (p q : List (Command n)) (x : Basis n) :
    eval (p++q) x = eval q (eval p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih => exact ih _



namespace QMAPerfectCompleteness.Main.VariableAddition.Layout
end QMAPerfectCompleteness.Main.VariableAddition.Layout
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.VariableAddition QMAPerfectCompleteness.Main.VariableAddition.Layout
variable {r n : ℕ} (L : Layout r n)









lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.left_ne_carry (i : Fin r) (j : Fin (r+1)) : L.left i ≠ L.carry j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hi := i.isLt
  change i.val = 2*r+j.val at hv
  omega

lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.right_ne_carry (i : Fin r) (j : Fin (r+1)) : L.right i ≠ L.carry j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hi := i.isLt
  change r+i.val = 2*r+j.val at hv
  omega







@[simp] lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.step_zero (j : Fin r) : L.step j 0 = L.left j := rfl
@[simp] lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.step_one (j : Fin r) : L.step j 1 = L.right j := rfl
@[simp] lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.step_two (j : Fin r) : L.step j 2 = L.carry j.castSucc := rfl
@[simp] lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.step_three (j : Fin r) : L.step j 3 = L.carry j.succ := rfl
@[simp] lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.step_four (j : Fin r) : L.step j 4 = L.temp := rfl





lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_succ (t : ℕ) (ht : t+1 ≤ r) (x : Basis n) :
    eval (L.carryPrefix (t+1) ht) x =
      eval (carryCommands (L.step ⟨t,by omega⟩)) (eval (L.carryPrefix t (by omega)) x) := by
  rw [carryPrefix,eval_append]


/-- Only positive carry wires below the current prefix can change. -/
theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_outside (t : ℕ) (ht : t ≤ r) (x : Basis n) (w : Fin n)
    (hw : ∀ j : Fin r, j.val < t → w ≠ L.carry j.succ) :
    eval (L.carryPrefix t ht) x w = x w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [carryPrefix_succ,carryCommands_eval]
    simp only [step_three]
    rw [Function.update_of_ne (hw ⟨t,by omega⟩ (Nat.lt_succ_self t))]
    exact ih (by omega) (fun j hj => hw j (by omega))

@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_left (t : ℕ) (ht : t ≤ r) (x : Basis n) (j : Fin r) :
    eval (L.carryPrefix t ht) x (L.left j) = x (L.left j) :=
  L.carryPrefix_outside t ht x _ (fun _ _ => L.left_ne_carry _ _)

@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_right (t : ℕ) (ht : t ≤ r) (x : Basis n) (j : Fin r) :
    eval (L.carryPrefix t ht) x (L.right j) = x (L.right j) :=
  L.carryPrefix_outside t ht x _ (fun _ _ => L.right_ne_carry _ _)



@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_output (t : ℕ) (ht : t ≤ r) (x : Basis n) (j : Fin r) :
    eval (L.carryPrefix t ht) x (L.output j) = x (L.output j) :=
  L.carryPrefix_outside t ht x _ (fun _ _ => L.output_ne_carry _ _)






@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.leftWord_bit (x : Basis n) (j : Fin r) :
    (L.leftWord x).getLsbD j = x (L.left j) := by
  simp only [leftWord,BitVec.getLsbD_ofNatLT]
  exact littleValue_decode _ j

@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.rightWord_bit (x : Basis n) (j : Fin r) :
    (L.rightWord x).getLsbD j = x (L.right j) := by
  simp only [rightWord,BitVec.getLsbD_ofNatLT]
  exact littleValue_decode _ j



lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.output_injective : Function.Injective L.output := by
  intro i j h
  have hv := congrArg Fin.val (L.slots.injective h)
  exact Fin.ext (by dsimp at hv; omega)





lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.temp_ne_output (j : Fin r) : L.temp ≠ L.output j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hj := j.isLt
  change 4*r+1 = 3*r+1+j.val at hv
  omega





lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.sumStep_eval (j : Fin r) (x : Basis n) : eval (L.sumStep j) x =
    Function.update x (L.output j) (xor (x (L.output j))
      (xor (x (L.left j)) (xor (x (L.right j)) (x (L.carry j.castSucc))))) := by
  simp [sumStep,eval,evalCommand,Function.update_of_ne (L.right_ne_output j j),
    Function.update_of_ne (L.output_ne_carry j j.castSucc).symm,Function.update_idem,Bool.xor_assoc]





lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.sumCommands_cons (j : Fin r) (js : List (Fin r)) (x : Basis n) :
    eval (L.sumCommands (j::js)) x = eval (L.sumCommands js) (eval (L.sumStep j) x) := by
  exact eval_append _ _ _

theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.sumCommands_output (js : List (Fin r)) (hjs : js.Nodup) (x : Basis n) (j : Fin r) :
    eval (L.sumCommands js) x (L.output j) =
      if j ∈ js then xor (x (L.output j))
        (xor (x (L.left j)) (xor (x (L.right j)) (x (L.carry j.castSucc)))) else x (L.output j) := by
  induction js generalizing x j with
  | nil => simp [sumCommands,eval]
  | cons i js ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hjs
    rw [sumCommands_cons,sumStep_eval,ih hn]
    simp only [Function.update_of_ne (L.left_ne_output j i),
      Function.update_of_ne (L.right_ne_output j i),
      Function.update_of_ne (L.output_ne_carry i j.castSucc).symm]
    by_cases he : j=i
    · subst j
      simp [hi]
    · have ho : L.output j ≠ L.output i := fun h => he (L.output_injective h)
      simp [he,ho]





lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.carryCommands_within (j : Fin r) :
    ∀ c ∈ carryCommands (L.step j), c.Within L.inputFrame := by
  simp [carryCommands,Command.Within,step_zero,step_one,step_two,step_three,step_four,
    inputFrame,L.left_ne_output,L.right_ne_output,L.temp_ne_output,
    fun i k => (L.output_ne_carry k i).symm]

lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_within (t : ℕ) (ht : t ≤ r) :
    ∀ c ∈ L.carryPrefix t ht, c.Within L.inputFrame := by
  induction t with
  | zero => simp [carryPrefix]
  | succ t ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact ih (by omega) c hc
    · exact L.carryCommands_within _ c hc













/-- On clean arithmetic workspace, output bits receive the exact binary sum by XOR. -/
theorem solution (x : Basis n) (hcarry : ∀ j, x (L.carry j) = false)
    (hp : x L.temp = false) (j : Fin r) :
    eval L.commands x (L.output j) =
      xor (x (L.output j)) ((L.leftWord x + L.rightWord x).getLsbD j) := by
  let p := L.carryPrefix r le_rfl
  let q := L.sumCommands (List.finRange r)
  change eval (p++q++p.reverse) x (L.output j) = _
  rw [eval_append,eval_append]
  have hrev : eval p.reverse (eval q (eval p x)) (L.output j) = eval q (eval p x) (L.output j) := by
    apply BooleanCircuits.eval_outside
    intro c hc hbad
    have hwithin := L.carryPrefix_within r le_rfl c (List.mem_reverse.mp hc)
    have ht : c.target ∈ L.inputFrame := by cases c <;> simp_all [Command.Within,Command.target]
    exact ht j hbad.symm
  rw [hrev]
  change eval (L.sumCommands (List.finRange r)) (eval (L.carryPrefix r le_rfl) x) (L.output j) = _
  rw [L.sumCommands_output (List.finRange r) (List.nodup_finRange r)]
  simp only [List.mem_finRange,if_true]
  rw [carryPrefix_output,carryPrefix_left,carryPrefix_right,
    carryPrefix_carry L r le_rfl x hcarry hp j.castSucc (Nat.le_of_lt j.isLt)]
  have hs := BitVec.getLsbD_add j.isLt (L.leftWord x) (L.rightWord x)
  simp only [leftWord_bit,rightWord_bit] at hs
  simp only [Fin.val_castSucc]
  rw [hs]
