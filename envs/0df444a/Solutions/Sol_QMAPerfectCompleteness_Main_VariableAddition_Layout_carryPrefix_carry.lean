-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_carry
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:54:17.354906+00:00
-- url     : https://prove2.me/submissions/b75bd63a-9135-4de2-b436-bf4e4524c5cc

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

lemma QMAPerfectCompleteness.Main.VariableAddition.carryBit_atLeastTwo (a b c : Bool) : carryBit a b c = Bool.atLeastTwo a b c := by
  cases a <;> cases b <;> cases c <;> rfl

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







lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.carry_injective : Function.Injective L.carry := by
  intro i j h
  have hv := congrArg Fin.val (L.slots.injective h)
  exact Fin.ext (by dsimp at hv; omega)

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

lemma QMAPerfectCompleteness.Main.VariableAddition.Layout.temp_ne_carry (j : Fin (r+1)) : L.temp ≠ L.carry j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hj := j.isLt
  change 4*r+1 = 2*r+j.val at hv
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

@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_temp (t : ℕ) (ht : t ≤ r) (x : Basis n) :
    eval (L.carryPrefix t ht) x L.temp = x L.temp :=
  L.carryPrefix_outside t ht x _ (fun _ _ => L.temp_ne_carry _)



theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_future (t : ℕ) (ht : t ≤ r) (x : Basis n) (j : Fin (r+1)) (hj : t < j.val) :
    eval (L.carryPrefix t ht) x (L.carry j) = x (L.carry j) := by
  apply L.carryPrefix_outside t ht x
  intro i hi h
  have hv := congrArg Fin.val (L.carry_injective h)
  change j.val = i.val+1 at hv
  omega




@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.leftWord_bit (x : Basis n) (j : Fin r) :
    (L.leftWord x).getLsbD j = x (L.left j) := by
  simp only [leftWord,BitVec.getLsbD_ofNatLT]
  exact littleValue_decode _ j

@[simp] theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.rightWord_bit (x : Basis n) (j : Fin r) :
    (L.rightWord x).getLsbD j = x (L.right j) := by
  simp only [rightWord,BitVec.getLsbD_ofNatLT]
  exact littleValue_decode _ j

/-- The actual carry chain agrees with binary addition, including its overflow carry. -/
theorem solution (t : ℕ) (ht : t ≤ r) (x : Basis n)
    (hcarry : ∀ j, x (L.carry j) = false) (hp : x L.temp = false)
    (j : Fin (r+1)) (hj : j.val ≤ t) :
    eval (L.carryPrefix t ht) x (L.carry j) =
      BitVec.carry j.val (L.leftWord x) (L.rightWord x) false := by
  induction t generalizing j with
  | zero =>
    have h : j = 0 := Fin.ext (by simpa using Nat.eq_zero_of_le_zero hj)
    subst j
    simpa [carryPrefix,eval] using hcarry 0
  | succ t ih =>
    rw [carryPrefix_succ,carryCommands_eval]
    simp only [step_zero,step_one,step_two,step_three,step_four]
    by_cases he : j = (⟨t,by omega⟩ : Fin r).succ
    · rw [he,Function.update_self]
      rw [carryPrefix_future L t (by omega) x _ (Nat.lt_succ_self t),hcarry,
        carryPrefix_left,carryPrefix_right,carryPrefix_temp,hp,ih (by omega) _ (by simp)]
      simp only [Bool.false_xor]
      simp only [Fin.val_succ,Fin.val_castSucc,Fin.val_mk]
      rw [BitVec.carry_succ]
      have h0 := L.leftWord_bit x (⟨t,by omega⟩ : Fin r)
      have h1 := L.rightWord_bit x (⟨t,by omega⟩ : Fin r)
      rw [h0,h1]
      exact carryBit_atLeastTwo _ _ _
    · rw [Function.update_of_ne (fun h => he (L.carry_injective h))]
      exact ih (by omega) j (by have hne : j.val ≠ t+1 := fun h => he (Fin.ext h); omega)
