-- Prove2me | solution 1 for StochasticProg.LShaped.thm2_finite_convergence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T00:00:00.790607+00:00
-- url     : https://prove2.me/submissions/3c8613c0-0fdb-4b88-85b9-828b4f320903

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

/-! Disproof of cea35418 `StochasticProg.LShaped.thm2_finite_convergence`.

The statement has no boundedness hypothesis, and its conclusion always ends in
"`K1 ∩ K2 = ∅`" or "some `x ∈ K1 ∩ K2` minimises `obj` over `K1 ∩ K2`". Both fail for an
unbounded problem, whatever the path. Take `n1 = 1`, `m1 = n2 = m2 = 0`, `K = 1`,
`c = (-1)`, `p = 1`. Every second-stage LP is the trivial one on `Fin 0`, so `Q ≡ 0`,
`K2 = univ`, `K1 = {x | 0 ≤ x₀}`, `obj x = -x₀`. `0 ∈ K1 ∩ K2`, and for any `x ∈ K1 ∩ K2`
the point `x + 1` lies in `K1 ∩ K2` and has `obj (x + 1) = -x₀ - 1 < obj x`. -/

set_option autoImplicit false

open StochasticProg.Recourse StochasticProg.LShaped

noncomputable def lsInst_cea3 : Instance 1 0 0 0 1 where
  A := 0
  b := 0
  c := fun _ => -1
  W := 0
  q := fun _ => 0
  h := fun _ => 0
  T := fun _ => 0
  p := fun _ => 1
  hp_nonneg := fun _ => zero_le_one
  hp_sum := by simp

theorem ls_QVal_cea3 (x : Fin 1 → ℝ) (k : Fin 1) : QVal lsInst_cea3 x k = 0 := by
  unfold QVal
  have hset : {z : EReal | ∃ y : Fin 0 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec lsInst_cea3.W y = lsInst_cea3.h k - Matrix.mulVec (lsInst_cea3.T k) x ∧
      z = ((dotProduct (lsInst_cea3.q k) y : ℝ) : EReal)} = {0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, -, -, rfl⟩
      simp [dotProduct]
    · rintro rfl
      exact ⟨0, fun i => i.elim0, Subsingleton.elim _ _, by simp [dotProduct]⟩
  rw [hset, sInf_singleton]

theorem ls_Q_cea3 (x : Fin 1 → ℝ) : Q lsInst_cea3 x = 0 := by
  unfold Q
  simp [ls_QVal_cea3, bookAdd]

open StochasticProg.LShaped StochasticProg.Recourse in
theorem solution : ¬ (∀ {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K),
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (Fin K × FeasBasis n2 m2) + Fintype.card (Fin K → Basis n2 m2) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsMasterInfeasible inst (path N).1 ∧ K1 inst ∩ K2 inst = ∅) ∨
        (∃ x θ, IsMasterOptimal inst (path N).1 (path N).2 x θ ∧
          x ∈ K1 inst ∩ K2 inst ∧
          (∀ β, IsOptimalAt inst x β →
            θ ≥ (optCutCoeffs inst β).2 - dotProduct (optCutCoeffs inst β).1 x) ∧
          ∀ x' ∈ K1 inst ∩ K2 inst, obj inst x ≤ obj inst x'))) := by
  intro H
  obtain ⟨N, path, -, -, -, -, hdisj⟩ := H lsInst_cea3
  have hK2 : ∀ x : Fin 1 → ℝ, x ∈ K2 lsInst_cea3 := by
    intro x
    simp [K2, ls_Q_cea3]
  have h0mem : (0 : Fin 1 → ℝ) ∈ K1 lsInst_cea3 ∩ K2 lsInst_cea3 :=
    ⟨⟨Subsingleton.elim _ _, fun _ => le_rfl⟩, hK2 0⟩
  rcases hdisj with ⟨-, hempty⟩ | ⟨x, θ, -, hx, -, hmin⟩
  · rw [hempty] at h0mem
    exact h0mem
  · have hx' : (fun i => x i + 1) ∈ K1 lsInst_cea3 ∩ K2 lsInst_cea3 :=
      ⟨⟨Subsingleton.elim _ _, fun i => by have := hx.1.2 i; linarith⟩, hK2 _⟩
    have h1 := hmin _ hx'
    simp only [obj, ls_Q_cea3, add_zero] at h1
    have h2 := EReal.coe_le_coe_iff.mp h1
    simp [lsInst_cea3, dotProduct] at h2
    linarith
