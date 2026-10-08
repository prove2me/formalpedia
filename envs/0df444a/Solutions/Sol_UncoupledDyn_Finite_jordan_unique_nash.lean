-- Prove2me | solution 1 for UncoupledDyn.Finite.jordan_unique_nash
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:53.870626+00:00
-- url     : https://prove2.me/submissions/ca52802e-7db8-415a-83da-c2192fe582f5

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix
import Definitions.Def_UncoupledDyn_Finite_Setting

open UncoupledDyn.Finite
set_option maxHeartbeats 1000000

private theorem payoff_formula (a x : Fin 3 → ℝ) (i : Fin 3) :
    expPayoff (jordanGame a) i x =
      x i * a i * (1 - x (i + 1)) + (1 - x i) * x (i + 1) := by
  classical
  have hu : (Finset.univ : Finset Profile) =
      {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
       ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} := by decide
  unfold expPayoff
  rw [hu]
  fin_cases i <;>
    norm_num [jordanGame, Finset.sum_insert, Fin.prod_univ_succ,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.add_def] <;>
      (try simp only [Fin.reduceFinMk]) <;>
      ring

private theorem deviation_formula (a x : Fin 3 → ℝ) (i : Fin 3) (y : ℝ) :
    expPayoff (jordanGame a) i (Function.update x i y) =
      y * a i * (1 - x (i + 1)) + (1 - y) * x (i + 1) := by
  rw [payoff_formula]
  have hn : i + 1 ≠ i := by fin_cases i <;> decide
  simp [hn]

private theorem best_response (a x : Fin 3 → ℝ) (hn : IsNash (jordanGame a) x) (i : Fin 3) :
    0 ≤ x i * (a i - (a i + 1) * x (i + 1)) ∧
      (1 - x i) * (a i - (a i + 1) * x (i + 1)) ≤ 0 := by
  have h0 := hn.2 i 0 (by constructor <;> norm_num)
  have h1 := hn.2 i 1 (by constructor <;> norm_num)
  rw [deviation_formula, payoff_formula] at h0 h1
  constructor <;> nlinarith

private theorem nash_interior (a x : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hn : IsNash (jordanGame a) x) : ∀ i, 0 < x i ∧ x i < 1 := by
  have hx (i : Fin 3) : 0 ≤ x i ∧ x i ≤ 1 := hn.1 i (by simp)
  have hzero (i : Fin 3) : x i ≠ 0 := by
    intro hi
    have b0 := best_response a x hn i
    have b1 := best_response a x hn (i + 1)
    have b2 := best_response a x hn (i + 1 + 1)
    have hc : i + 1 + 1 + 1 = i := by fin_cases i <;> decide
    rw [hc] at b2
    have hxp : 0 < x (i + 1) := by
      have h := hx (i + 1)
      rw [hi] at b0
      nlinarith [ha i]
    have hC : 0 ≤ a (i + 1) - (a (i + 1) + 1) * x (i + 1 + 1) :=
      nonneg_of_mul_nonneg_right b1.1 hxp
    have hxlt : x (i + 1 + 1) < 1 := by
      nlinarith [ha (i + 1)]
    have hC2 : a (i + 1 + 1) - (a (i + 1 + 1) + 1) * x i ≤ 0 :=
      nonpos_of_mul_nonpos_right b2.2 (by linarith)
    rw [hi] at hC2
    nlinarith [ha (i + 1 + 1)]
  have hone (i : Fin 3) : x i ≠ 1 := by
    intro hi
    have b0 := best_response a x hn i
    have b1 := best_response a x hn (i + 1)
    have b2 := best_response a x hn (i + 1 + 1)
    have hc : i + 1 + 1 + 1 = i := by fin_cases i <;> decide
    rw [hc] at b2
    have hxlt : x (i + 1) < 1 := by
      rw [hi] at b0
      nlinarith [ha i]
    have hC : a (i + 1) - (a (i + 1) + 1) * x (i + 1 + 1) ≤ 0 :=
      nonpos_of_mul_nonpos_right b1.2 (by linarith)
    have hxp : 0 < x (i + 1 + 1) := by
      nlinarith [ha (i + 1)]
    have hC2 : 0 ≤ a (i + 1 + 1) - (a (i + 1 + 1) + 1) * x i :=
      nonneg_of_mul_nonneg_right b2.1 hxp
    rw [hi] at hC2
    nlinarith
  intro i
  exact ⟨lt_of_le_of_ne (hx i).1 (Ne.symm (hzero i)),
    lt_of_le_of_ne (hx i).2 (hone i)⟩

private theorem jordan_characterization (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (x : Fin 3 → ℝ) :
    IsNash (jordanGame a) x ↔ x = fun i => a (i - 1) / (a (i - 1) + 1) := by
  constructor
  · intro hn
    have hint := nash_interior a x ha hn
    have he (i : Fin 3) : x (i + 1) = a i / (a i + 1) := by
      have hb := best_response a x hn i
      have hp : 0 ≤ a i - (a i + 1) * x (i + 1) :=
        nonneg_of_mul_nonneg_right hb.1 (hint i).1
      have hm : a i - (a i + 1) * x (i + 1) ≤ 0 :=
        nonpos_of_mul_nonpos_right hb.2 (by linarith [(hint i).2])
      apply (eq_div_iff (by linarith [ha i] : a i + 1 ≠ 0)).2
      nlinarith
    funext i
    have hc : i - 1 + 1 = i := by fin_cases i <;> decide
    simpa only [hc] using he (i - 1)
  · intro he
    subst x
    constructor
    · intro i _
      constructor
      · exact le_of_lt (div_pos (ha _) (by linarith [ha (i - 1)]))
      · apply (div_le_one (by linarith [ha (i - 1)])).2
        linarith
    · intro i y hy
      rw [deviation_formula, payoff_formula]
      have hc : i + 1 - 1 = i := by fin_cases i <;> decide
      simp only [hc]
      have hz : a i - (a i + 1) * (a i / (a i + 1)) = 0 := by
        field_simp [ne_of_gt (by linarith [ha i] : 0 < a i + 1)]
        ring
      have heq : a i * (1 - a i / (a i + 1)) = a i / (a i + 1) := by
        nlinarith
      rw [mul_assoc, heq, mul_assoc, heq]
      ring_nf
      rfl

theorem solution (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    (∀ x : Fin 3 → ℝ, IsNash (jordanGame a) x ↔ x = fun i => a (i - 1) / (a (i - 1) + 1)) ∧
    (∀ x : Fin 3 → ℝ, IsNash Gamma0 x ↔ x = fun _ => (1 / 2 : ℝ)) := by
  refine ⟨jordan_characterization a ha, ?_⟩
  intro x
  convert jordan_characterization (fun _ => 1) (by intro i; norm_num) x using 1 <;> norm_num [Gamma0]

#print axioms solution
