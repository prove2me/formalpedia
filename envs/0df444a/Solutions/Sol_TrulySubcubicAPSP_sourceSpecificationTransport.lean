-- Prove2me | solution 1 for TrulySubcubicAPSP.sourceSpecificationTransport
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T06:13:24.402107+00:00
-- url     : https://prove2.me/submissions/6fd32b6b-0d15-48a5-a361-1a966ef8b393

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Transport from the original paper's word RAM and problem statements to the
mission's separately declared copies. No algorithm or running-time result is
assumed here: every theorem below preserves the source proof's exact step bound.
-/

namespace APSPProofBridge

/-- The instruction correspondence preserves each operand and branch target. -/
def instruction : EndStatement.Instr → TrulySubcubicAPSP.Instr
  | .one i => .one i
  | .add i j k => .add i j k
  | .sub i j k => .sub i j k
  | .mul i j k => .mul i j k
  | .load i j => .load i j
  | .store i j => .store i j
  | .bltz i l => .bltz i l
  | .accept => .accept
  | .reject => .reject

/-- Map every instruction, preserving program length and every program position. -/
def program (P : List EndStatement.Instr) : List TrulySubcubicAPSP.Instr :=
  P.map instruction

theorem loadWords (W : Nat) (ws : List Int) :
    TrulySubcubicAPSP.loadWords W ws = EndStatement.loadWords W ws := rfl

theorem instructionAt (P : List EndStatement.Instr) (pc : Nat) :
    (program P).getD pc .reject = instruction (P.getD pc .reject) := by
  induction P generalizing pc with
  | nil => simp [program, instruction]
  | cons i P ih =>
    cases pc with
    | zero => simp [program]
    | succ pc => simpa [program] using ih pc

/-- The copied machine executes the mapped program identically, at every word
width, time bound, program counter, and initial memory. -/
theorem exec {W : Nat} (P : List EndStatement.Instr) (t pc : Nat)
    (m : Int → BitVec W) :
    TrulySubcubicAPSP.exec (program P) t pc m = EndStatement.exec P t pc m := by
  induction t generalizing pc m with
  | zero => rfl
  | succ t ih =>
    simp only [TrulySubcubicAPSP.exec, EndStatement.exec, instructionAt]
    cases P.getD pc .reject <;> simp only [instruction] <;> try rfl
    all_goals apply ih

/-- Instance conversion together with matching input, verdict, and output
specifications suffices to transport an execution witness. -/
theorem solvedBy {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {n : Nat} (x : R.Instance n) (P : List EndStatement.Instr) (W t : Nat)
    (h : Q.SolvedBy (f x) P W t) : R.SolvedBy x (program P) W t := by
  obtain ⟨verdict, m, run, correct, output⟩ := h
  refine ⟨verdict, m, ?_, correct.trans (yes_iff x), ?_⟩
  · rw [exec, loadWords, ← input_eq x]
    exact run
  · apply (output_iff x _).mp
    simpa only [input_eq x] using output

/-- Transport preserves the program's step bound, width bound, exponent, and all
quantifiers over input magnitudes, sizes, instances, and word widths. -/
theorem solvedInTime {Q : EndStatement.Problem} {R : TrulySubcubicAPSP.Problem}
    (f : ∀ {n : Nat}, R.Instance n → Q.Instance n)
    (input_eq : ∀ {n : Nat} (x : R.Instance n), Q.input (f x) = R.input x)
    (yes_iff : ∀ {n : Nat} (x : R.Instance n), Q.yes (f x) ↔ R.yes x)
    (output_iff : ∀ {n : Nat} (x : R.Instance n) (out : Nat → Int),
      Q.output (f x) out ↔ R.output x out)
    {r : Rat} (h : Q.SolvedInTime r) : R.SolvedInTime r := by
  intro κ
  obtain ⟨P, b, T, bound, correct⟩ := h κ
  refine ⟨program P, b, T, bound, ?_⟩
  intro n x magnitude W width
  apply solvedBy f input_eq yes_iff output_iff
  apply correct n (f x) _ W width
  simpa only [input_eq x] using magnitude

/-- Exact Triangle has the same instances, input encoding, and verdict. -/
theorem exactTriangle {r : Rat}
    (h : EndStatement.ExactTriangle.SolvedInTime r) :
    TrulySubcubicAPSP.ExactTriangle.SolvedInTime r :=
  solvedInTime (fun x => x) (fun _ => rfl) (fun _ => Iff.rfl)
    (fun _ _ => Iff.rfl) h

/-- The min-plus product has the same instances, input encoding, and outputs. -/
theorem minPlus {r : Rat}
    (h : EndStatement.MinPlusProduct.SolvedInTime r) :
    TrulySubcubicAPSP.MinPlusProduct.SolvedInTime r :=
  solvedInTime (fun x => x) (fun _ => rfl) (fun _ => Iff.rfl)
    (fun _ _ => Iff.rfl) h

/-- Every original path is a mission path of the same weight and endpoints. -/
theorem pathToMission {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} (h : EndStatement.Path w i j d) :
    TrulySubcubicAPSP.Path w i j d := by
  induction h with
  | nil i => exact .nil i
  | cons edge _ ih => exact .cons edge ih

/-- Every mission path is an original path of the same weight and endpoints. -/
theorem pathToOriginal {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} (h : TrulySubcubicAPSP.Path w i j d) :
    EndStatement.Path w i j d := by
  induction h with
  | nil i => exact .nil i
  | cons edge _ ih => exact .cons edge ih

theorem path_iff {n : Nat} {w : Fin n → Fin n → Option Int}
    {i j : Fin n} {d : Int} :
    EndStatement.Path w i j d ↔ TrulySubcubicAPSP.Path w i j d :=
  ⟨pathToMission, pathToOriginal⟩

/-- Change only the proof of the no-negative-cycle promise. -/
def apspInstance {n : Nat} (x : TrulySubcubicAPSP.APSP.Instance n) :
    EndStatement.APSP.Instance n :=
  ⟨x.val, fun i d h => x.property i d (pathToMission h)⟩

theorem apspOutput {n : Nat} (x : TrulySubcubicAPSP.APSP.Instance n)
    (out : Nat → Int) :
    EndStatement.APSP.output (apspInstance x) out ↔
      TrulySubcubicAPSP.APSP.output x out := by
  simp only [EndStatement.APSP, TrulySubcubicAPSP.APSP, apspInstance, path_iff]

/-- APSP transport includes the graph promise, reachability flags, attained
minimum distances, and unreachable pairs. -/
theorem apsp {r : Rat} (h : EndStatement.APSP.SolvedInTime r) :
    TrulySubcubicAPSP.APSP.SolvedInTime r :=
  solvedInTime apspInstance (fun _ => rfl) (fun _ => Iff.rfl) apspOutput h

end APSPProofBridge


theorem solution :
    (∀ r : Rat, EndStatement.ExactTriangle.SolvedInTime r →
      TrulySubcubicAPSP.ExactTriangle.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.MinPlusProduct.SolvedInTime r →
      TrulySubcubicAPSP.MinPlusProduct.SolvedInTime r) ∧
    (∀ r : Rat, EndStatement.APSP.SolvedInTime r →
      TrulySubcubicAPSP.APSP.SolvedInTime r) := by
  exact ⟨fun _ h => APSPProofBridge.exactTriangle h,
    fun _ h => APSPProofBridge.minPlus h, fun _ h => APSPProofBridge.apsp h⟩

#print axioms solution
