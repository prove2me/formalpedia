-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P29.wpicc_noncontractivity
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:57:21.9197+00:00
-- url     : https://prove2.me/submissions/0d8c70ef-1987-4516-8294-79ef844fff26

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P29
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P29.S04

open QAlgorithms.Papers.Independent.Advance50.P47
  (IsCorrelation IsNoSignaling TwoLocalBoxes losrTransform)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

abbrev sourceScenario : BellScenario :=
  ⟨2, 1, 2, 2, by decide, by decide, by decide, by decide⟩

abbrev targetScenario : BellScenario :=
  ⟨1, 1, 2, 1, by decide, by decide, by decide, by decide⟩

/-- Alice always outputs zero; Bob outputs a fair bit. -/
def p : Behavior sourceScenario :=
  fun _ _ a _ => if a = 0 then 1 / 2 else 0

/-- Alice is fair exactly when her setting equals Bob's fair output. -/
def q : Behavior sourceScenario :=
  fun x _ a b => if b = x then 1 / 4 else if a = 0 then 1 / 2 else 0

theorem p_ns : IsNS p := by
  constructor
  · constructor
    · intro x y a b
      fin_cases a <;> norm_num [p]
    · intro x y
      norm_num [p, Fin.sum_univ_two]
  · constructor
    · intro x z y b
      rfl
    · intro y z x a
      rfl

theorem q_ns : IsNS q := by
  constructor
  · constructor
    · intro x y a b
      fin_cases x <;> fin_cases a <;> fin_cases b <;> norm_num [q]
    · intro x y
      change (∑ a : Fin 2, ∑ b : Fin 2, q x y a b) = 1
      fin_cases x <;> norm_num [q, Fin.sum_univ_two]
  · constructor
    · intro x z y b
      fin_cases x <;> fin_cases z <;> fin_cases b <;>
        norm_num [q, Fin.sum_univ_two]
    · intro y z x a
      rfl

/-- Bob measures first and tells Alice which of her settings to use. -/
def prepared : Preparation sourceScenario targetScenario :=
  .bobFirst 0 (fun b => .measure b (fun a _ => a) (fun _ _ => 0))

def w : BellOperation sourceScenario targetScenario := prepared.apply

theorem w_apply (r : Behavior sourceScenario) (x : targetScenario.X)
    (y : targetScenario.Y) (a : targetScenario.A) (b : targetScenario.B) :
    w r x y a b = ∑ j : sourceScenario.B, r j 0 a j := by
  fin_cases b
  fin_cases a <;>
    simp [w, prepared, Preparation.apply, bobContribution, responseIndicator]

/-- A fixed unused LOSR branch; weight one selects the preparation branch. -/
def unusedLocal : TwoLocalBoxes sourceScenario.X sourceScenario.Y
    sourceScenario.A sourceScenario.B targetScenario.X targetScenario.Y
    targetScenario.A targetScenario.B Unit Unit where
  inputLaw := PMF.pure ()
  outputLaw := PMF.pure ()
  inputAlice := fun _ _ _ => 1 / 2
  inputBob := fun _ _ _ => 1
  outputAlice := fun _ _ _ _ _ => 1 / 2
  outputBob := fun _ _ _ _ _ => 1
  inputAlice_law := by intro l x; norm_num [IsLaw, Fin.sum_univ_two]
  inputBob_law := by intro l y; simp [IsLaw]
  outputAlice_law := by intro l a x u; norm_num [IsLaw, Fin.sum_univ_two]
  outputBob_law := by intro l b y v; simp [IsLaw]

theorem w_wpicc : IsWPICC w := by
  refine ⟨1, by norm_num, le_rfl, losrTransform unusedLocal,
    ⟨Unit, Unit, unusedLocal, fun _ => rfl⟩,
    Unit, PMF.pure (), fun _ => prepared, ?_, ?_⟩
  · intro l
    trivial
  · intro r hr x y a b
    simp [w]

theorem input_kl (x : sourceScenario.X) (y : sourceScenario.Y) :
    classicalRelativeEntropyNats (fun z : sourceScenario.A × sourceScenario.B =>
      p x y z.1 z.2) (fun z => q x y z.1 z.2) =
        ENNReal.ofReal (Real.log 2 / 2) := by
  change classicalRelativeEntropyNats (fun z : Fin 2 × Fin 2 => p x y z.1 z.2)
    (fun z : Fin 2 × Fin 2 => q x y z.1 z.2) = _
  fin_cases x <;> fin_cases y
  all_goals
    norm_num [classicalRelativeEntropyNats, p, q, sourceScenario,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.exists_fin_two]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring

theorem input_sb : sb p q = ENNReal.ofReal (Real.log 2 / 2) := by
  simp only [sb, input_kl]
  simp [sourceScenario]

theorem output_p (x : targetScenario.X) (y : targetScenario.Y)
    (a : targetScenario.A) (b : targetScenario.B) :
    w p x y a b = if a = 0 then 1 else 0 := by
  rw [w_apply]
  fin_cases a <;> norm_num [p, Fin.sum_univ_two]

theorem output_q (x : targetScenario.X) (y : targetScenario.Y)
    (a : targetScenario.A) (b : targetScenario.B) :
    w q x y a b = 1 / 2 := by
  rw [w_apply]
  fin_cases a <;> norm_num [q, Fin.sum_univ_two]

theorem output_kl (x : targetScenario.X) (y : targetScenario.Y) :
    classicalRelativeEntropyNats (fun z : targetScenario.A × targetScenario.B =>
      w p x y z.1 z.2) (fun z => w q x y z.1 z.2) =
        ENNReal.ofReal (Real.log 2) := by
  simp only [classicalRelativeEntropyNats, output_p, output_q]
  norm_num [targetScenario, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem output_sb : sb (w p) (w q) = ENNReal.ofReal (Real.log 2) := by
  simp only [sb, output_kl]
  simp [targetScenario]

theorem witness :
    ∃ (s t : BellScenario) (w : BellOperation s t) (p q : Behavior s),
      IsWPICC w ∧ IsNS p ∧ IsNS q ∧ sb p q < sb (w p) (w q) := by
  refine ⟨sourceScenario, targetScenario, w, p, q, w_wpicc, p_ns, q_ns, ?_⟩
  rw [input_sb, output_sb]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (ENNReal.ofReal_lt_ofReal_iff hlog).mpr
  linarith

end QAlgorithms.Papers.Independent.Intakethird100.P29.S04


open QAlgorithms.Papers.Independent.Intakethird100.P29

/-- A Bob-first prepared wiring strictly increases the optimized box divergence. -/
theorem solution :
    ∃ (s t : BellScenario) (w : BellOperation s t) (p q : Behavior s),
      IsWPICC w ∧ IsNS p ∧ IsNS q ∧ sb p q < sb (w p) (w q) :=
  S04.witness

#print axioms solution
