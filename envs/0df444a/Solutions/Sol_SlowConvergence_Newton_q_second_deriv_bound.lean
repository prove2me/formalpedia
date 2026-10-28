-- Prove2me | solution 1 for SlowConvergence.Newton.q_second_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:04:53.719848+00:00
-- url     : https://prove2.me/submissions/194aa557-0c97-4019-a8bd-b3b72e5ff1eb

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace Aux_SCNqi

noncomputable def P (A B C D E F : ℝ) (t : ℝ) : ℝ :=
  A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4 + F * t ^ 5

lemma hasDerivAt_P (A B C D E F t : ℝ) :
    HasDerivAt (P A B C D E F) (P B (2 * C) (3 * D) (4 * E) (5 * F) 0 t) t := by
  have h := ((((((hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B)).add
    ((hasDerivAt_pow 2 t).const_mul C)).add ((hasDerivAt_pow 3 t).const_mul D)).add
    ((hasDerivAt_pow 4 t).const_mul E)).add ((hasDerivAt_pow 5 t).const_mul F))
  have hf : (P A B C D E F) = (fun x => (fun _ => A) x + B * id x + C * x ^ 2 + D * x ^ 3
      + E * x ^ 4 + F * x ^ 5) := by
    funext x; simp [P]
  rw [hf]
  refine h.congr_deriv ?_
  unfold P
  first
    | ring
    | (norm_num; ring)
    | norm_num

lemma deriv_P (A B C D E F : ℝ) :
    deriv (P A B C D E F) = P B (2 * C) (3 * D) (4 * E) (5 * F) 0 := by
  funext t
  exact (hasDerivAt_P A B C D E F t).deriv

end Aux_SCNqi

open SlowConvergence.Newton Aux_SCNqi in
theorem solution (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (q k)) t| ≤ 219 := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hq : q k = P (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2) (-((1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2)
      (1 / 2 * (9 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (-16 * (1 / ((k : ℝ) + 2)) ^ 2 + 2 * (1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (7 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)) := by
    funext t; unfold q P; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ha0 : 0 ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
  have hb0 : 0 ≤ (1 / ((k : ℝ) + 2)) ^ 2 := by positivity
  have ha1 : (1 / ((k : ℝ) + 1)) ^ 2 ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [div_le_one (by positivity)]; linarith
  have hb1 : (1 / ((k : ℝ) + 2)) ^ 2 ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    rw [div_le_one (by positivity)]; linarith
  rw [hq, deriv_P, deriv_P]
  unfold P
  generalize (1 / ((k : ℝ) + 1)) ^ 2 = a at *
  generalize (1 / ((k : ℝ) + 2)) ^ 2 = b at *
  have t2 : 0 ≤ t ^ 2 := by positivity
  have t3 : 0 ≤ t ^ 3 := by positivity
  have t2' : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have t3' : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
  have p1 := mul_le_mul_of_nonneg_left ht1 ha0
  have p2 := mul_le_mul_of_nonneg_left t2' ha0
  have p3 := mul_le_mul_of_nonneg_left t3' ha0
  have p4 := mul_le_mul_of_nonneg_left ht1 hb0
  have p5 := mul_le_mul_of_nonneg_left t2' hb0
  have p6 := mul_le_mul_of_nonneg_left t3' hb0
  have q1 := mul_nonneg ha0 ht0
  have q2 := mul_nonneg ha0 t2
  have q3 := mul_nonneg ha0 t3
  have q4 := mul_nonneg hb0 ht0
  have q5 := mul_nonneg hb0 t2
  have q6 := mul_nonneg hb0 t3
  rw [abs_le]
  constructor <;> nlinarith
