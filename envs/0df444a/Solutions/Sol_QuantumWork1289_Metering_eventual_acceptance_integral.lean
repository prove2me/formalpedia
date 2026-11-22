-- Prove2me | solution 1 for QuantumWork1289.Metering.eventual_acceptance_integral
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:46:40.058413+00:00
-- url     : https://prove2.me/submissions/baea8178-cecc-4866-88b6-ac2264c03220

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment

set_option autoImplicit false
open QuantumWork1289.Metering MeasureTheory
open scoped ENNReal


open Classical in
private noncomputable def acceptedWeight {O : Type} {n : ℕ}
    (P : O → Prop) (z : Terminal O n) : ℝ≥0∞ :=
  match z.output with
  | none => 0
  | some o => if P o then branchMass z else 0

private theorem stepwise {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (f : X → B) (P : O → Prop) (t : ℕ)
    (s : S) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ((execute A f t s ρ).map (acceptedWeight P)).sum ≤
      ((execute A f (t+1) s ρ).map (acceptedWeight P)).sum := by
  induction t generalizing s ρ with
  | zero => simp [execute, acceptedWeight]
  | succ t ih =>
    conv_lhs => rw [execute]
    conv_rhs => rw [execute]
    cases ha : A.step s with
    | halt o => exact le_rfl
    | privateOp b M next =>
      simp only [List.map_flatten, List.map_ofFn, List.sum_flatten, List.sum_ofFn]
      exact Finset.sum_le_sum fun j _ => ih (next j) _
    | classicalRead x next =>
      simp only [List.map_map]
      exact ih (next (f x)) ρ
    | coherentCall w next =>
      simp only [List.map_map]
      exact ih next _

theorem horizon_mono {X B O S : Type} [Fintype B] [DecidableEq B] [AddCommGroup B]
    {n : ℕ} (A : HybridMachine X B O S n) (ρ : InitialState n)
    (accept : (X → B) → O → Prop) (f : X → B) :
    Monotone (fun t => acceptedMass A ρ accept t f) :=
  monotone_nat_of_le_succ (fun t => stepwise A f (accept f) t A.initial ρ.matrix)

theorem solution {X B O Ω S : Type} [Fintype B] [Nonempty B] [DecidableEq B]
    [AddCommGroup B] [MeasurableSpace B] [MeasurableSpace Ω]
    {n : ℕ} (A : SeededMachine X B O Ω S n) (μ : Measure Ω)
    (accept : (X → B) → O → Prop) (h : MeasurableExecution A μ accept) :
    (∀ ω f, Monotone (fun t => acceptedMass (A.machine ω) (A.initialState ω) accept t f)) ∧
      successProbability A μ accept = ∫⁻ p : Ω × (X → B),
        ⨆ t : ℕ, acceptedMass (A.machine p.1) (A.initialState p.1) accept t p.2
        ∂(μ.prod (oracleLaw X B)) := by
  refine ⟨fun ω f => horizon_mono _ _ _ _, ?_⟩
  exact (lintegral_iSup' h (Filter.Eventually.of_forall
    (fun p => horizon_mono (A.machine p.1) (A.initialState p.1) accept p.2))).symm

#print axioms solution
