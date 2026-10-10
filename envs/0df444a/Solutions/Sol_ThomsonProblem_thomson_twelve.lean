-- Prove2me | solution 1 for ThomsonProblem.thomson_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:44:08.784027+00:00
-- url     : https://prove2.me/submissions/7dd6cbf1-b14b-463b-b824-8f6ed04f57de

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem.N12

/-- `s = 1/√5`, written through the golden ratio. -/
noncomputable def s : ℝ := Real.goldenRatio / (Real.goldenRatio + 2)

/-- `p = √(2 - 2s)`, the chordal distance between icosahedron neighbours. -/
noncomputable def p : ℝ := Real.sqrt (2 - 2 * s)

lemma s_sq : s ^ 2 = 1 / 5 := by
  have h := Real.goldenRatio_sq
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  unfold s
  rw [div_pow, div_eq_div_iff (by positivity) (by norm_num)]
  nlinarith [h]

lemma s_pos : 0 < s := by
  unfold s; have := Real.goldenRatio_pos; positivity

lemma s_lo : (44721 / 100000 : ℝ) < s := by nlinarith [s_sq, s_pos]
lemma s_hi : s < (44722 / 100000 : ℝ) := by nlinarith [s_sq, s_pos]

lemma p_sq : p ^ 2 = 2 - 2 * s := by
  unfold p; rw [Real.sq_sqrt]; linarith [s_hi]

lemma p_pos : 0 < p := by
  unfold p; apply Real.sqrt_pos.2; linarith [s_hi]

lemma p_lo : (10514 / 10000 : ℝ) < p := by nlinarith [p_sq, p_pos, s_hi]
lemma p_hi : p < (10515 / 10000 : ℝ) := by nlinarith [p_sq, p_pos, s_lo]

/-- The degree-5 Hermite interpolant of `t ↦ (2 - 2t)^(-1/2)` at `t ∈ {-1, -s, s}`. -/
noncomputable def a0 : ℝ := 275/512 * p * s + 125/512 * p + 25/128
noncomputable def a1 : ℝ := 925/512 * p * s - 325/512 * p + 21/128
noncomputable def a2 : ℝ := 825/256 * p * s + 175/256 * p - 125/64
noncomputable def a3 : ℝ := -125/256 * p * s + 525/256 * p - 105/64
noncomputable def a4 : ℝ := -3125/512 * p * s - 875/512 * p + 625/128
noncomputable def a5 : ℝ := -1875/512 * p * s - 1125/512 * p + 525/128

noncomputable def fP (t : ℝ) : ℝ := a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 + a4 * t ^ 4 + a5 * t ^ 5

noncomputable def q0 : ℝ := 5/64
noncomputable def q1 : ℝ := 675/1024 * p * s + 225/1024 * p - 95/256
noncomputable def q2 : ℝ := -525/512 * p * s - 175/512 * p + 175/128 * s + 25/64
noncomputable def q3 : ℝ := 125/512 * p * s + 325/1024 * p - 225/256 * s + 25/1024
noncomputable def q4 : ℝ := 375/2048 * p * s + 225/2048 * p - 375/512 * s + 75/512
noncomputable def q5 : ℝ := -1875/16384 * p * s - 1125/16384 * p + 525/4096

lemma ps_lo : (10514 / 10000 : ℝ) * (44721 / 100000) < p * s := by
  nlinarith [p_lo, s_lo, mul_lt_mul'' p_lo s_lo (by norm_num) (by norm_num)]
lemma ps_hi : p * s < (10515 / 10000 : ℝ) * (44722 / 100000) := by
  nlinarith [p_hi, s_hi, mul_lt_mul'' p_hi s_hi p_pos.le s_pos.le]

lemma a0_nonneg : 0 ≤ a0 := by unfold a0; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma a1_nonneg : 0 ≤ a1 := by unfold a1; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma a2_nonneg : 0 ≤ a2 := by unfold a2; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma a3_nonneg : 0 ≤ a3 := by unfold a3; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma a4_nonneg : 0 ≤ a4 := by unfold a4; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma a5_nonneg : 0 ≤ a5 := by unfold a5; linarith [ps_lo, ps_hi, p_lo, p_hi]
lemma q1_nonneg : 0 ≤ q1 := by unfold q1; linarith [ps_lo, ps_hi, p_lo, p_hi, s_lo, s_hi]
lemma q2_nonneg : 0 ≤ q2 := by unfold q2; linarith [ps_lo, ps_hi, p_lo, p_hi, s_lo, s_hi]
lemma q3_nonneg : 0 ≤ q3 := by unfold q3; linarith [ps_lo, ps_hi, p_lo, p_hi, s_lo, s_hi]
lemma q4_nonneg : 0 ≤ q4 := by unfold q4; linarith [ps_lo, ps_hi, p_lo, p_hi, s_lo, s_hi]
lemma q5_nonneg : 0 ≤ q5 := by unfold q5; linarith [ps_lo, ps_hi, p_lo, p_hi, s_lo, s_hi]

/-- `m = √(2 + 2s)`, the chordal distance between second neighbours. -/
noncomputable def m : ℝ := p * (1 + 5 * s) / 2

lemma kernel_identity (u : ℝ) :
    1 - u * fP (1 - u ^ 2 / 2) = ((u - 2) * (u - p) * (u - m)) ^ 2 *
      (q0 + q1 * u + q2 * u ^ 2 + q3 * u ^ 3 + q4 * u ^ 4 + q5 * u ^ 5) := by
  unfold fP a0 a1 a2 a3 a4 a5 q0 q1 q2 q3 q4 q5 m
  linear_combination (46875*p^3*s^3*u^7/65536 - 65625*p^3*s^3*u^6/16384 + 96875*p^3*s^3*u^5/16384 + 8125*p^3*s^3*u^4/1024 - 146875*p^3*s^3*u^3/4096 + 43125*p^3*s^3*u^2/1024 - 16875*p^3*s^3*u/1024 + 46875*p^3*s^2*u^7/65536 - 65625*p^3*s^2*u^6/16384 + 79375*p^3*s^2*u^5/16384 + 5375*p^3*s^2*u^4/512 - 131875*p^3*s^2*u^3/4096 + 31625*p^3*s^2*u^2/1024 - 12375*p^3*s^2*u/1024 + 13125*p^3*s*u^7/65536 - 18375*p^3*s*u^6/16384 + 20125*p^3*s*u^5/16384 + 3325*p^3*s*u^4/1024 - 35125*p^3*s*u^3/4096 + 7475*p^3*s*u^2/1024 - 2925*p^3*s*u/1024 + 1125*p^3*u^7/65536 - 1575*p^3*u^6/16384 + 1625*p^3*u^5/16384 + 75*p^3*u^4/256 - 2925*p^3*u^3/4096 + 575*p^3*u^2/1024 - 225*p^3*u/1024 - 46875*p^2*s^3*u^8/32768 + 65625*p^2*s^3*u^7/8192 - 59375*p^2*s^3*u^6/8192 - 29375*p^2*s^3*u^5/1024 + 121875*p^2*s^3*u^4/2048 - 14375*p^2*s^3*u^3/512 - 625*p^2*s^3*u^2/512 - 65625*p^2*s^2*u^8/32768 + 170625*p^2*s^2*u^7/16384 - 84375*p^2*s^2*u^6/8192 - 65875*p^2*s^2*u^5/2048 + 169375*p^2*s^2*u^4/2048 - 7875*p^2*s^2*u^3/128 + 2125*p^2*s^2*u^2/512 + 2875*p^2*s^2*u/256 - 125*p^2*s^2/64 - 28125*p^2*s*u^8/32768 + 18375*p^2*s*u^7/4096 - 35125*p^2*s*u^6/8192 - 7175*p^2*s*u^5/512 + 70625*p^2*s*u^4/2048 - 13175*p^2*s*u^3/512 + 1825*p^2*s*u^2/512 + 575*p^2*s*u/128 - 25*p^2*s/32 - 3375*p^2*u^8/32768 + 8925*p^2*u^7/16384 - 4125*p^2*u^6/8192 - 3575*p^2*u^5/2048 + 8325*p^2*u^4/2048 - 745*p^2*u^3/256 + 275*p^2*u^2/512 + 115*p^2*u/256 - 5*p^2/64 - 46875*p*s^4*u^7/32768 + 65625*p*s^4*u^6/8192 - 96875*p*s^4*u^5/8192 - 8125*p*s^4*u^4/512 + 146875*p*s^4*u^3/2048 - 43125*p*s^4*u^2/512 + 16875*p*s^4*u/512 + 46875*p*s^3*u^9/65536 - 65625*p*s^3*u^8/16384 - 53125*p*s^3*u^7/16384 + 34375*p*s^3*u^6/1024 - 38125*p*s^3*u^5/4096 - 77125*p*s^3*u^4/1024 + 45625*p*s^3*u^3/1024 + 2875*p*s^3*u^2/128 - 1125*p*s^3*u/128 + 121875*p*s^2*u^9/65536 - 144375*p*s^2*u^8/16384 + 28125*p*s^2*u^7/8192 + 152875*p*s^2*u^6/4096 - 106125*p*s^2*u^5/2048 - 25*p*s^2*u^4/1024 + 4125*p*s^2*u^3/512 + 6325*p*s^2*u^2/256 - 3725*p*s^2*u/256 + 80625*p*s*u^9/65536 - 91875*p*s*u^8/16384 + 59625*p*s*u^7/16384 + 19775*p*s*u^6/1024 - 165375*p*s*u^5/4096 + 24625*p*s*u^4/1024 + 4275*p*s*u^3/1024 - 575*p*s*u^2/128 - 275*p*s*u/128 + 14625*p*u^9/65536 - 17325*p*u^8/16384 + 25375*p*u^7/32768 + 29025*p*u^6/8192 - 63625*p*u^5/8192 + 5255*p*u^4/1024 + 825*p*u^3/2048 - 805*p*u^2/512 + 15*p*u/512 + 46875*s^4*u^8/16384 - 65625*s^4*u^7/4096 + 59375*s^4*u^6/4096 + 29375*s^4*u^5/512 - 121875*s^4*u^4/1024 + 14375*s^4*u^3/256 + 625*s^4*u^2/256 + 46875*s^3*u^8/8192 - 144375*s^3*u^7/8192 - 3125*s^3*u^6/512 + 64625*s^3*u^5/1024 - 20625*s^3*u^4/256 + 17125*s^3*u^3/256 - 1375*s^3*u^2/128 - 2875*s^3*u/128 + 125*s^3/32 - 9375*s^2*u^10/16384 + 39375*s^2*u^9/16384 + 18125*s^2*u^8/4096 - 162375*s^2*u^7/8192 - 27125*s^2*u^6/2048 + 55075*s^2*u^5/1024 + 11125*s^2*u^4/512 - 7725*s^2*u^3/128 - 25*s^2*u^2/32 + 1725*s^2*u/128 - 75*s^2/32 - 5625*s*u^10/8192 + 18375*s*u^9/8192 + 5125*s*u^8/8192 - 64225*s*u^7/8192 + 3375*s*u^6/512 - 3925*s*u^5/1024 + 4175*s*u^4/256 - 5935*s*u^3/256 + 275*s*u^2/128 + 1035*s*u/128 - 45*s/32 - 3375*u^10/16384 + 12075*u^9/16384 - 3375*u^8/16384 - 18575*u^7/8192 + 19275*u^6/4096 - 4365*u^5/1024 + 625*u^4/1024 + 5*u^3/256 + 15*u^2/256 + 115*u/128 - 5/32) * p_sq + (46875*p*s^3*u^7/16384 - 65625*p*s^3*u^6/4096 + 96875*p*s^3*u^5/4096 + 8125*p*s^3*u^4/256 - 146875*p*s^3*u^3/1024 + 43125*p*s^3*u^2/256 - 16875*p*s^3*u/256 - 46875*p*s^2*u^9/32768 + 65625*p*s^2*u^8/8192 + 59375*p*s^2*u^7/16384 - 209375*p*s^2*u^6/4096 - 20625*p*s^2*u^5/4096 + 60875*p*s^2*u^4/512 + 55625*p*s^2*u^3/1024 - 54625*p*s^2*u^2/256 + 21375*p*s^2*u/256 - 9375*p*s*u^9/4096 + 39375*p*s*u^8/4096 - 209375*p*s*u^7/16384 - 43875*p*s*u^6/4096 + 367625*p*s*u^5/4096 - 36925*p*s*u^4/256 + 45375*p*s*u^3/1024 + 7475*p*s*u^2/256 - 425*p*s*u/256 - 88125*p*u^9/32768 + 44625*p*u^8/8192 + 165125*p*u^7/16384 - 78325*p*u^6/4096 + 14125*p*u^5/4096 - 12475*p*u^4/512 + 19075*p*u^3/1024 + 4025*p*u^2/256 - 2075*p*u/256 - 46875*s^3*u^8/8192 + 65625*s^3*u^7/2048 - 59375*s^3*u^6/2048 - 29375*s^3*u^5/256 + 121875*s^3*u^4/512 - 14375*s^3*u^3/128 - 625*s^3*u^2/128 - 46875*s^2*u^8/8192 + 13125*s^2*u^7/4096 + 84375*s^2*u^6/2048 - 5875*s^2*u^5/512 - 39375*s^2*u^4/512 - 1375*s^2*u^3/64 + 3375*s^2*u^2/128 + 2875*s^2*u/64 - 125*s^2/16 + 9375*s*u^10/8192 - 39375*s*u^9/8192 + 11875*s*u^8/8192 + 22125*s*u^7/2048 + 17375*s*u^6/2048 - 275*s*u^5/64 - 80375*s*u^4/512 + 7425*s*u^3/32 - 2675*s*u^2/128 - 575*s*u/8 + 25*s/2 + 1875*u^10/8192 + 2625*u^9/8192 + 52875*u^8/8192 - 95525*u^7/4096 - 64375*u^6/2048 + 57825*u^5/512 - 2325*u^4/512 - 10065*u^3/128 - 75*u^2/128 + 1265*u/64 - 55/16) * s_sq

lemma kernel_le {u : ℝ} (hu : 0 < u) : fP (1 - u ^ 2 / 2) ≤ 1 / u := by
  have hq : 0 ≤ q0 + q1 * u + q2 * u ^ 2 + q3 * u ^ 3 + q4 * u ^ 4 + q5 * u ^ 5 := by
    have := q1_nonneg; have := q2_nonneg; have := q3_nonneg; have := q4_nonneg
    have := q5_nonneg; have : (0:ℝ) ≤ q0 := by norm_num [q0]
    positivity
  have h := kernel_identity u
  rw [le_div_iff₀ hu]
  nlinarith [mul_nonneg (sq_nonneg ((u - 2) * (u - p) * (u - m))) hq]

end ThomsonProblem.N12

namespace ThomsonProblem.N12

open ThomsonProblem

lemma inner3 (x z : Space) : inner ℝ x z = x 0 * z 0 + x 1 * z 1 + x 2 * z 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ]; ring

lemma normsq3 (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_succ]; ring

lemma sum_form {N n : ℕ} (y : Fin N → Space) (D : Fin n → ℝ) (g : Fin n → Space → ℝ)
    (F : ℝ → ℝ) (hF : ∀ x z : Space, F (inner ℝ x z) = ∑ α, D α * (g α x * g α z)) :
    ∑ i, ∑ j, F (inner ℝ (y i) (y j)) = ∑ α, D α * (∑ i, g α (y i)) ^ 2 := by
  simp_rw [hF]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, ∑ α, D α * (g α (y i) * g α (y j))
      = ∑ α, ∑ i, D α * (g α (y i) * g α (y j)) := fun j => Finset.sum_comm
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

lemma moment1_eq {N : ℕ} (y : Fin N → Space) :
    ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 1 =
      ∑ α, (![1, 1, 1] : Fin 3 → ℝ) α *
        (∑ i, (![(fun x : Space => x 0), (fun x : Space => x 1), (fun x : Space => x 2)] : Fin 3 → Space → ℝ) α (y i)) ^ 2 :=
  sum_form y _ _ (fun t => t ^ 1) (fun x z => by simp [Fin.sum_univ_succ, inner3]; ring)

lemma moment2_eq {N : ℕ} (y : Fin N → Space) :
    ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 2 =
      ∑ α, (![1, 1, 1, 2, 2, 2] : Fin 6 → ℝ) α *
        (∑ i, (![(fun x : Space => x 0 ^ 2), (fun x : Space => x 1 ^ 2), (fun x : Space => x 2 ^ 2), (fun x : Space => x 0 * x 1), (fun x : Space => x 0 * x 2), (fun x : Space => x 1 * x 2)] : Fin 6 → Space → ℝ) α (y i)) ^ 2 :=
  sum_form y _ _ (fun t => t ^ 2) (fun x z => by simp [Fin.sum_univ_succ, inner3]; ring)

lemma moment3_eq {N : ℕ} (y : Fin N → Space) :
    ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 3 =
      ∑ α, (![1, 3, 3, 3, 6, 3, 1, 3, 3, 1] : Fin 10 → ℝ) α *
        (∑ i, (![(fun x : Space => x 0 ^ 3), (fun x : Space => x 0 ^ 2 * x 1), (fun x : Space => x 0 ^ 2 * x 2), (fun x : Space => x 0 * x 1 ^ 2), (fun x : Space => x 0 * x 1 * x 2), (fun x : Space => x 0 * x 2 ^ 2), (fun x : Space => x 1 ^ 3), (fun x : Space => x 1 ^ 2 * x 2), (fun x : Space => x 1 * x 2 ^ 2), (fun x : Space => x 2 ^ 3)] : Fin 10 → Space → ℝ) α (y i)) ^ 2 :=
  sum_form y _ _ (fun t => t ^ 3) (fun x z => by simp [Fin.sum_univ_succ, inner3]; ring)

lemma moment4_eq {N : ℕ} (y : Fin N → Space) :
    ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 4 =
      ∑ α, (![1, 1, 1, 6, 6, 6, 4, 4, 12, 4, 12, 12, 4, 4, 4] : Fin 15 → ℝ) α *
        (∑ i, (![(fun x : Space => x 0 ^ 4), (fun x : Space => x 1 ^ 4), (fun x : Space => x 2 ^ 4), (fun x : Space => x 0 ^ 2 * x 1 ^ 2), (fun x : Space => x 0 ^ 2 * x 2 ^ 2), (fun x : Space => x 1 ^ 2 * x 2 ^ 2), (fun x : Space => x 0 ^ 3 * x 1), (fun x : Space => x 0 ^ 3 * x 2), (fun x : Space => x 0 ^ 2 * x 1 * x 2), (fun x : Space => x 0 * x 1 ^ 3), (fun x : Space => x 0 * x 1 ^ 2 * x 2), (fun x : Space => x 0 * x 1 * x 2 ^ 2), (fun x : Space => x 0 * x 2 ^ 3), (fun x : Space => x 1 ^ 3 * x 2), (fun x : Space => x 1 * x 2 ^ 3)] : Fin 15 → Space → ℝ) α (y i)) ^ 2 :=
  sum_form y _ _ (fun t => t ^ 4) (fun x z => by simp [Fin.sum_univ_succ, inner3]; ring)

lemma moment5_eq {N : ℕ} (y : Fin N → Space) :
    ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 5 =
      ∑ α, (![1, 5, 5, 10, 20, 10, 10, 30, 30, 10, 5, 20, 30, 20, 5, 1, 5, 10, 10, 5, 1] : Fin 21 → ℝ) α *
        (∑ i, (![(fun x : Space => x 0 ^ 5), (fun x : Space => x 0 ^ 4 * x 1), (fun x : Space => x 0 ^ 4 * x 2), (fun x : Space => x 0 ^ 3 * x 1 ^ 2), (fun x : Space => x 0 ^ 3 * x 1 * x 2), (fun x : Space => x 0 ^ 3 * x 2 ^ 2), (fun x : Space => x 0 ^ 2 * x 1 ^ 3), (fun x : Space => x 0 ^ 2 * x 1 ^ 2 * x 2), (fun x : Space => x 0 ^ 2 * x 1 * x 2 ^ 2), (fun x : Space => x 0 ^ 2 * x 2 ^ 3), (fun x : Space => x 0 * x 1 ^ 4), (fun x : Space => x 0 * x 1 ^ 3 * x 2), (fun x : Space => x 0 * x 1 ^ 2 * x 2 ^ 2), (fun x : Space => x 0 * x 1 * x 2 ^ 3), (fun x : Space => x 0 * x 2 ^ 4), (fun x : Space => x 1 ^ 5), (fun x : Space => x 1 ^ 4 * x 2), (fun x : Space => x 1 ^ 3 * x 2 ^ 2), (fun x : Space => x 1 ^ 2 * x 2 ^ 3), (fun x : Space => x 1 * x 2 ^ 4), (fun x : Space => x 2 ^ 5)] : Fin 21 → Space → ℝ) α (y i)) ^ 2 :=
  sum_form y _ _ (fun t => t ^ 5) (fun x z => by simp [Fin.sum_univ_succ, inner3]; ring)

lemma moment1_nonneg {N : ℕ} (y : Fin N → Space) :
    0 ≤ ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 1 := by
  rw [moment1_eq]; simp only [Fin.sum_univ_succ]; simp; positivity

lemma moment3_nonneg {N : ℕ} (y : Fin N → Space) :
    0 ≤ ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 3 := by
  rw [moment3_eq]; simp only [Fin.sum_univ_succ]; simp; positivity

lemma moment5_nonneg {N : ℕ} (y : Fin N → Space) :
    0 ≤ ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 5 := by
  rw [moment5_eq]; simp only [Fin.sum_univ_succ]; simp; positivity

lemma moment2_ge {N : ℕ} (y : Fin N → Space) (hy : ∀ i, ‖y i‖ = 1) :
    (N : ℝ) ^ 2 / 3 ≤ ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 2 := by
  have hN : ∑ i, (y i 0 ^ 2 + y i 1 ^ 2 + y i 2 ^ 2) = (N : ℝ) := by
    simp_rw [← normsq3, hy]; simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hN
  rw [moment2_eq]; simp only [Fin.sum_univ_succ]; simp
  set A := ∑ i, y i 0 ^ 2
  set B := ∑ i, y i 1 ^ 2
  set C := ∑ i, y i 2 ^ 2
  rw [← hN]
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C),
    sq_nonneg (∑ i, y i 0 * y i 1), sq_nonneg (∑ i, y i 0 * y i 2),
    sq_nonneg (∑ i, y i 1 * y i 2)]

lemma moment4_ge {N : ℕ} (y : Fin N → Space) (hy : ∀ i, ‖y i‖ = 1) :
    (N : ℝ) ^ 2 / 5 ≤ ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 4 := by
  have hN : ∑ i, (y i 0 ^ 4 + y i 1 ^ 4 + y i 2 ^ 4 + 2 * (y i 0 ^ 2 * y i 1 ^ 2)
      + 2 * (y i 0 ^ 2 * y i 2 ^ 2) + 2 * (y i 1 ^ 2 * y i 2 ^ 2)) = (N : ℝ) := by
    have : ∀ i, y i 0 ^ 4 + y i 1 ^ 4 + y i 2 ^ 4 + 2 * (y i 0 ^ 2 * y i 1 ^ 2)
      + 2 * (y i 0 ^ 2 * y i 2 ^ 2) + 2 * (y i 1 ^ 2 * y i 2 ^ 2) = (‖y i‖ ^ 2) ^ 2 := by
      intro i; rw [normsq3]; ring
    simp_rw [this, hy]; simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hN
  rw [moment4_eq]; simp only [Fin.sum_univ_succ]; simp
  set A := ∑ i, y i 0 ^ 4
  set B := ∑ i, y i 1 ^ 4
  set C := ∑ i, y i 2 ^ 4
  set D := ∑ i, y i 0 ^ 2 * y i 1 ^ 2
  set E := ∑ i, y i 0 ^ 2 * y i 2 ^ 2
  set F := ∑ i, y i 1 ^ 2 * y i 2 ^ 2
  rw [← hN]
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C),
    sq_nonneg (A - 3 * D), sq_nonneg (A - 3 * E), sq_nonneg (A - 3 * F),
    sq_nonneg (B - 3 * D), sq_nonneg (B - 3 * E), sq_nonneg (B - 3 * F),
    sq_nonneg (C - 3 * D), sq_nonneg (C - 3 * E), sq_nonneg (C - 3 * F),
    sq_nonneg (D - E), sq_nonneg (D - F), sq_nonneg (E - F),
    sq_nonneg (∑ i, y i 0 ^ 3 * y i 1), sq_nonneg (∑ i, y i 0 ^ 3 * y i 2),
    sq_nonneg (∑ i, y i 0 * y i 1 ^ 3), sq_nonneg (∑ i, y i 1 ^ 3 * y i 2),
    sq_nonneg (∑ i, y i 0 * y i 2 ^ 3), sq_nonneg (∑ i, y i 1 * y i 2 ^ 3),
    sq_nonneg (∑ i, y i 0 ^ 2 * y i 1 * y i 2), sq_nonneg (∑ i, y i 0 * y i 1 ^ 2 * y i 2),
    sq_nonneg (∑ i, y i 0 * y i 1 * y i 2 ^ 2)]

end ThomsonProblem.N12

namespace ThomsonProblem.N12

open ThomsonProblem

lemma two_mul_coulombEnergy {N : ℕ} (x : Fin N → Space) :
    2 * coulombEnergy x = ∑ i, ∑ j, 1 / dist (x i) (x j) := by
  unfold coulombEnergy
  have key : ∀ i, ∑ j, 1 / dist (x i) (x j)
      = ∑ j ∈ Finset.Ioi i, 1 / dist (x i) (x j) + ∑ j ∈ Finset.Iio i, 1 / dist (x i) (x j) := by
    intro i
    have h1 : (Finset.univ : Finset (Fin N)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [h1, Finset.sum_union, Finset.sum_union]
    · simp
    · simp
    · rw [Finset.disjoint_left]; intro a ha; simp at ha ⊢; omega
  simp_rw [key, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, 1 / dist (x i) (x j)
      = ∑ i, ∑ j ∈ Finset.Ioi i, 1 / dist (x i) (x j) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp at hp ⊢; exact hp
    · intro p hp; simp at hp ⊢; exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [dist_comm]
  rw [hswap]; ring

lemma dist_sq_eq {x z : Space} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    dist x z ^ 2 = 2 - 2 * inner ℝ x z := by
  rw [dist_eq_norm, @norm_sub_sq_real, hx, hz]; ring

lemma pair_bound {x z : Space} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hxz : x ≠ z) :
    fP (inner ℝ x z) ≤ 1 / dist x z := by
  have hu : 0 < dist x z := dist_pos.2 hxz
  have ht : inner ℝ x z = 1 - dist x z ^ 2 / 2 := by rw [dist_sq_eq hx hz]; ring
  rw [ht]; exact kernel_le hu

/-- The linear-programming lower bound for any admissible configuration. -/
theorem lp_bound {N : ℕ} (y : Fin N → Space) (hy : IsAdmissible y) :
    (N : ℝ) ^ 2 * (a0 + a2 / 3 + a4 / 5) - N * fP 1 ≤ 2 * coulombEnergy y := by
  rw [two_mul_coulombEnergy]
  have hpt : ∀ i j, fP (inner ℝ (y i) (y j)) - (if i = j then fP 1 else 0)
      ≤ 1 / dist (y i) (y j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [hy.1 i]
    · simp only [hij, if_false, sub_zero]
      exact pair_bound (hy.1 i) (hy.1 j) (fun h => hij (hy.2 h))
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpt i j
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hexp : ∑ i, ∑ j, fP (inner ℝ (y i) (y j)) = (N : ℝ) ^ 2 * a0
      + a1 * ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 1
      + a2 * ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 2 + a3 * ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 3
      + a4 * ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 4 + a5 * ∑ i, ∑ j, inner ℝ (y i) (y j) ^ 5 := by
    unfold fP
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, pow_one]
    ring
  have h1 := mul_nonneg a1_nonneg (moment1_nonneg y)
  have h3 := mul_nonneg a3_nonneg (moment3_nonneg y)
  have h5 := mul_nonneg a5_nonneg (moment5_nonneg y)
  have h2 := mul_le_mul_of_nonneg_left (moment2_ge y hy.1) a2_nonneg
  have h4 := mul_le_mul_of_nonneg_left (moment4_ge y hy.1) a4_nonneg
  nlinarith [hsum, hexp]

end ThomsonProblem.N12

namespace ThomsonProblem.N12

open ThomsonProblem

/-- The unnormalised icosahedron vertices. -/
noncomputable def rawV : Fin 12 → Space :=
  ![!₂[0, 1, Real.goldenRatio], !₂[0, 1, -Real.goldenRatio],
      !₂[0, -1, Real.goldenRatio], !₂[0, -1, -Real.goldenRatio],
      !₂[1, Real.goldenRatio, 0], !₂[1, -Real.goldenRatio, 0],
      !₂[-1, Real.goldenRatio, 0], !₂[-1, -Real.goldenRatio, 0],
      !₂[Real.goldenRatio, 0, 1], !₂[Real.goldenRatio, 0, -1],
      !₂[-Real.goldenRatio, 0, 1], !₂[-Real.goldenRatio, 0, -1]]

/-- Which of the four inner-product values `1, s, -s, -1` a pair of vertices realises. -/
def icoCode : Fin 12 → Fin 12 → Fin 4 :=
  ![![0, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2],
    ![2, 0, 3, 1, 1, 2, 1, 2, 2, 1, 2, 1],
    ![1, 3, 0, 2, 2, 1, 2, 1, 1, 2, 1, 2],
    ![3, 1, 2, 0, 2, 1, 2, 1, 2, 1, 2, 1],
    ![1, 1, 2, 2, 0, 2, 1, 3, 1, 1, 2, 2],
    ![2, 2, 1, 1, 2, 0, 3, 1, 1, 1, 2, 2],
    ![1, 1, 2, 2, 1, 3, 0, 2, 2, 2, 1, 1],
    ![2, 2, 1, 1, 3, 1, 2, 0, 2, 2, 1, 1],
    ![1, 2, 1, 2, 1, 1, 2, 2, 0, 1, 2, 3],
    ![2, 1, 2, 1, 1, 1, 2, 2, 1, 0, 3, 2],
    ![1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 0, 1],
    ![2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 0]]

noncomputable def icoVal : Fin 4 → ℝ := ![1, s, -s, -1]

lemma one_add_gold_sq : 1 + Real.goldenRatio ^ 2 = Real.goldenRatio + 2 := by
  rw [Real.goldenRatio_sq]; ring

lemma ico_inner_raw (i j : Fin 12) :
    inner ℝ (regularIcosahedron i) (regularIcosahedron j)
      = (Real.goldenRatio + 2)⁻¹ * inner ℝ (rawV i) (rawV j) := by
  have hpos : (0:ℝ) < 1 + Real.goldenRatio ^ 2 := by positivity
  unfold regularIcosahedron
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← one_add_gold_sq]
  congr 1
  rw [← sq, div_pow, one_pow, Real.sq_sqrt hpos.le, one_div]

lemma ico_inner_row0 (j : Fin 12) :
    inner ℝ (regularIcosahedron 0) (regularIcosahedron j) = icoVal (icoCode 0 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row1 (j : Fin 12) :
    inner ℝ (regularIcosahedron 1) (regularIcosahedron j) = icoVal (icoCode 1 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row2 (j : Fin 12) :
    inner ℝ (regularIcosahedron 2) (regularIcosahedron j) = icoVal (icoCode 2 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row3 (j : Fin 12) :
    inner ℝ (regularIcosahedron 3) (regularIcosahedron j) = icoVal (icoCode 3 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row4 (j : Fin 12) :
    inner ℝ (regularIcosahedron 4) (regularIcosahedron j) = icoVal (icoCode 4 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row5 (j : Fin 12) :
    inner ℝ (regularIcosahedron 5) (regularIcosahedron j) = icoVal (icoCode 5 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row6 (j : Fin 12) :
    inner ℝ (regularIcosahedron 6) (regularIcosahedron j) = icoVal (icoCode 6 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row7 (j : Fin 12) :
    inner ℝ (regularIcosahedron 7) (regularIcosahedron j) = icoVal (icoCode 7 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row8 (j : Fin 12) :
    inner ℝ (regularIcosahedron 8) (regularIcosahedron j) = icoVal (icoCode 8 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row9 (j : Fin 12) :
    inner ℝ (regularIcosahedron 9) (regularIcosahedron j) = icoVal (icoCode 9 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row10 (j : Fin 12) :
    inner ℝ (regularIcosahedron 10) (regularIcosahedron j) = icoVal (icoCode 10 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner_row11 (j : Fin 12) :
    inner ℝ (regularIcosahedron 11) (regularIcosahedron j) = icoVal (icoCode 11 j) := by
  have h2 := Real.goldenRatio_sq
  have h3 : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    linear_combination Real.goldenRatio * h2 + h2
  have hpos : (0:ℝ) < Real.goldenRatio + 2 := by linarith [Real.goldenRatio_pos]
  have r2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * r2
  have r4 : Real.sqrt 5 ^ 4 = 25 := by linear_combination (Real.sqrt 5 ^ 2 + 5) * r2
  rw [ico_inner_raw, inner3]
  fin_cases j <;>
    simp [rawV, icoCode, icoVal, s] <;> field_simp <;> ring_nf <;> linarith [h2, h3, r2, r3, r4]

lemma ico_inner (i j : Fin 12) :
    inner ℝ (regularIcosahedron i) (regularIcosahedron j) = icoVal (icoCode i j) := by
  fin_cases i
  · exact ico_inner_row0 j
  · exact ico_inner_row1 j
  · exact ico_inner_row2 j
  · exact ico_inner_row3 j
  · exact ico_inner_row4 j
  · exact ico_inner_row5 j
  · exact ico_inner_row6 j
  · exact ico_inner_row7 j
  · exact ico_inner_row8 j
  · exact ico_inner_row9 j
  · exact ico_inner_row10 j
  · exact ico_inner_row11 j

end ThomsonProblem.N12

namespace ThomsonProblem.N12

open ThomsonProblem

lemma row_sum (H : Fin 4 → ℝ) (i : Fin 12) :
    ∑ j, H (icoCode i j) = H 0 + 5 * H 1 + 5 * H 2 + H 3 := by
  fin_cases i <;> simp [Fin.sum_univ_succ, icoCode] <;> ring

lemma icoCode_self (i : Fin 12) : icoCode i i = 0 := by
  revert i; decide

lemma icoCode_ne (i j : Fin 12) (h : i ≠ j) : icoCode i j ≠ 0 := by
  revert i j; decide

lemma ico_norm (i : Fin 12) : ‖regularIcosahedron i‖ = 1 := by
  have h := ico_inner i i
  rw [real_inner_self_eq_norm_sq, icoCode_self] at h
  have h1 : icoVal 0 = 1 := rfl
  rw [h1] at h
  nlinarith [norm_nonneg (regularIcosahedron i)]

lemma icoVal_eq_one {c : Fin 4} (h : icoVal c = 1) : c = 0 := by
  fin_cases c <;> simp [icoVal] at h ⊢ <;> linarith [s_lo, s_hi]

lemma ico_admissible : IsAdmissible regularIcosahedron := by
  refine ⟨ico_norm, fun i j hij => ?_⟩
  by_contra hne
  have h := ico_inner i j
  rw [hij, real_inner_self_eq_norm_sq, ico_norm] at h
  exact icoCode_ne i j hne (icoVal_eq_one (by rw [← h]; norm_num))

lemma m_sq : m ^ 2 = 2 + 2 * s := by
  unfold m; linear_combination (25 * s ^ 2 / 4 + 5 * s / 2 + 1 / 4) * p_sq + (15 / 2 - 25 * s / 2) * s_sq

lemma m_pos : 0 < m := by
  unfold m; have := p_pos; have := s_pos; positivity

lemma inv_p_eq : 1 / p = 5 * p * (1 + s) / 8 := by
  refine (eq_one_div_of_mul_eq_one_right ?_).symm
  linear_combination (5 * s / 8 + 5 / 8) * p_sq - 5 / 4 * s_sq

lemma inv_m_eq : 1 / m = 5 * p * s / 4 := by
  refine (eq_one_div_of_mul_eq_one_right ?_).symm
  unfold m
  linear_combination (25 * s ^ 2 / 8 + 5 * s / 8) * p_sq + (5 - 25 * s / 4) * s_sq

lemma ico_dist_inv (i j : Fin 12) :
    1 / dist (regularIcosahedron i) (regularIcosahedron j)
      = 1 / Real.sqrt (2 - 2 * icoVal (icoCode i j)) := by
  rw [← ico_inner, ← dist_sq_eq (ico_norm i) (ico_norm j), Real.sqrt_sq dist_nonneg]

lemma ico_two_energy :
    2 * coulombEnergy regularIcosahedron = (12 : ℝ) ^ 2 * (a0 + a2 / 3 + a4 / 5) - 12 * fP 1 := by
  rw [two_mul_coulombEnergy]
  simp_rw [ico_dist_inv]
  simp_rw [row_sum (fun c => 1 / Real.sqrt (2 - 2 * icoVal c))]
  have h1 : Real.sqrt (2 - 2 * icoVal 1) = p := rfl
  have h2 : Real.sqrt (2 - 2 * icoVal 2) = m := by
    rw [show 2 - 2 * icoVal 2 = m ^ 2 by rw [m_sq]; simp [icoVal]]
    exact Real.sqrt_sq m_pos.le
  have h3 : Real.sqrt (2 - 2 * icoVal 3) = 2 := by
    rw [show 2 - 2 * icoVal 3 = 2 ^ 2 by simp [icoVal]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h0 : Real.sqrt (2 - 2 * icoVal 0) = 0 := by simp [icoVal]
  rw [h0, h1, h2, h3, inv_p_eq, inv_m_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold fP a0 a2 a4 a1 a3 a5
  push_cast
  ring

/-- **Thomson problem, `N = 12`.** The regular icosahedron minimises the Coulomb energy. -/
theorem thomson_twelve : IsEnergyMinimizer regularIcosahedron := by
  refine ⟨ico_admissible, fun y hy => ?_⟩
  have h1 := lp_bound y hy
  have h2 := ico_two_energy
  push_cast at h1
  linarith

end ThomsonProblem.N12

/-- Thomson problem, `N = 12`: the regular icosahedron minimises the Coulomb energy among
all configurations of 12 distinct points on the unit sphere. -/
theorem solution : ThomsonProblem.IsEnergyMinimizer ThomsonProblem.regularIcosahedron :=
  ThomsonProblem.N12.thomson_twelve
