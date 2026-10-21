-- Prove2me | solution 1 for SherbrookeMetric.PointEstimate.worked_example
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:13:34.680584+00:00
-- url     : https://prove2.me/submissions/18c50d0b-edc4-4aa0-a2b8-7650ea8606f1

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders

set_option autoImplicit false
open SherbrookeMetric.PointEstimate ServiceParts.StockLevels

namespace SMPAux

lemma pmf_hasSum (a : ℝ) : HasSum (fun x : ℕ => poissonPmf a x) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (a : ℝ)).mul_left (Real.exp (-a))
  have e : Real.exp (-a) * NormedSpace.exp a = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]; simp
  rw [e] at h
  exact h.congr_fun (fun x => by unfold poissonPmf; ring)

lemma mean_hasSum (a : ℝ) : HasSum (fun x : ℕ => (x : ℝ) * poissonPmf a x) a := by
  have h := (pmf_hasSum a).mul_left a
  rw [mul_one] at h
  have e0 : a - ∑ i ∈ Finset.range 1, (i : ℝ) * poissonPmf a i = a := by simp
  have h3 : HasSum (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) * poissonPmf a (n + 1))
      (a - ∑ i ∈ Finset.range 1, (i : ℝ) * poissonPmf a i) := by
    rw [e0]
    refine h.congr_fun (fun n => ?_)
    unfold poissonPmf
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  exact (hasSum_nat_add_iff' 1).mp h3

/-- closed form of the backorder function, defined recursively in `s`. -/
noncomputable def G : ℕ → ℝ → ℝ
  | 0, a => a
  | s + 1, a => G s a - 1 + ∑ x ∈ Finset.range (s + 1), poissonPmf a x

lemma G_zero (a : ℝ) : G 0 a = a := rfl

lemma G_succ (s : ℕ) (a : ℝ) :
    G (s + 1) a = G s a - 1 + ∑ x ∈ Finset.range (s + 1), poissonPmf a x := rfl

lemma hasSum_term (s : ℕ) (a : ℝ) :
    HasSum (fun x : ℕ => if s < x then ((x : ℝ) - s) * poissonPmf a x else 0) (G s a) := by
  induction s with
  | zero =>
    rw [G_zero]
    refine (mean_hasSum a).congr_fun (fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    · have : 0 < x := Nat.pos_of_ne_zero hx
      simp [this]
  | succ s ih =>
    have hq : HasSum (fun x : ℕ => if s < x then poissonPmf a x else 0)
        (1 - ∑ x ∈ Finset.range (s + 1), poissonPmf a x) := by
      have h2 : HasSum (fun x : ℕ => if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)
          (∑ x ∈ Finset.range (s + 1), (if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
      have hs : ∑ x ∈ Finset.range (s + 1), (if x ∈ Finset.range (s + 1) then poissonPmf a x else 0)
          = ∑ x ∈ Finset.range (s + 1), poissonPmf a x :=
        Finset.sum_congr rfl (fun x hx => if_pos hx)
      rw [hs] at h2
      refine ((pmf_hasSum a).sub h2).congr_fun (fun x => ?_)
      by_cases hx : s < x
      · have : ¬ x ∈ Finset.range (s + 1) := by simp; omega
        simp [hx, this]
      · have : x ∈ Finset.range (s + 1) := by simp; omega
        simp [hx, this]
    have hG : G (s + 1) a = G s a - (1 - ∑ x ∈ Finset.range (s + 1), poissonPmf a x) := by
      rw [G_succ]; ring
    rw [hG]
    refine (ih.sub hq).congr_fun (fun x => ?_)
    by_cases h1 : s + 1 < x
    · have h2 : s < x := by omega
      simp only [if_pos h1, if_pos h2]; push_cast; ring
    · by_cases h2 : s < x
      · have : x = s + 1 := by omega
        subst this
        simp
      · simp [h1, h2]

lemma backorders_eq (s : ℕ) (a : ℝ) : backorders s a = G s a := (hasSum_term s a).tsum_eq

lemma backorders_funext (s : ℕ) : backorders s = G s := funext (backorders_eq s)

lemma pmf_deriv0 (a : ℝ) :
    HasDerivAt (fun μ : ℝ => poissonPmf μ 0) (-poissonPmf a 0) a := by
  have h := (Real.hasDerivAt_exp (-a)).comp a (hasDerivAt_neg a)
  have e : (fun μ : ℝ => poissonPmf μ 0) = fun μ => Real.exp (-μ) := by
    funext μ; simp [poissonPmf]
  rw [e]
  exact h.congr_deriv (by simp [poissonPmf])

lemma pmf_deriv_succ (n : ℕ) (a : ℝ) :
    HasDerivAt (fun μ : ℝ => poissonPmf μ (n + 1))
      (poissonPmf a n - poissonPmf a (n + 1)) a := by
  have h1 := (Real.hasDerivAt_exp (-a)).comp a (hasDerivAt_neg a)
  have h2 := hasDerivAt_pow (n + 1) a
  have h := (h1.mul h2).div_const ((n + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  unfold poissonPmf
  rw [Nat.factorial_succ]
  push_cast
  simp only [Function.comp_apply, Nat.add_sub_cancel]
  field_simp
  ring

lemma fill_deriv (n : ℕ) (a : ℝ) :
    HasDerivAt (fun μ : ℝ => ∑ x ∈ Finset.range (n + 1), poissonPmf μ x)
      (-poissonPmf a n) a := by
  induction n with
  | zero => simpa using pmf_deriv0 a
  | succ n ih =>
    have := ih.add (pmf_deriv_succ n a)
    have e : (fun μ : ℝ => ∑ x ∈ Finset.range (n + 1 + 1), poissonPmf μ x) =
        (fun μ : ℝ => ∑ x ∈ Finset.range (n + 1), poissonPmf μ x) +
          fun μ : ℝ => poissonPmf μ (n + 1) :=
      funext fun μ => Finset.sum_range_succ _ _
    rw [e]
    exact this.congr_deriv (by ring)

lemma G_deriv (s : ℕ) (a : ℝ) :
    HasDerivAt (G s) (1 - ∑ x ∈ Finset.range s, poissonPmf a x) a := by
  induction s with
  | zero =>
    have e : G 0 = fun x => x := funext fun _ => rfl
    rw [e]
    exact (hasDerivAt_id a).congr_deriv (by simp)
  | succ s ih =>
    have := (ih.sub_const 1).add (fill_deriv s a)
    have e : G (s + 1) = fun μ => G s μ - 1 + ∑ x ∈ Finset.range (s + 1), poissonPmf μ x := by
      funext μ; rfl
    rw [e]
    exact this.congr_deriv (by rw [Finset.sum_range_succ]; ring)

lemma deriv_backorders (s : ℕ) :
    deriv (backorders s) = fun μ => 1 - ∑ x ∈ Finset.range s, poissonPmf μ x := by
  funext μ
  rw [backorders_funext]
  exact (G_deriv s μ).deriv

lemma deriv2_backorders (n : ℕ) (a : ℝ) :
    HasDerivAt (deriv (backorders (n + 1))) (poissonPmf a n) a := by
  rw [deriv_backorders]
  exact ((hasDerivAt_const a (1 : ℝ)).sub (fill_deriv n a)).congr_deriv (by ring)

lemma diff_backorders (s : ℕ) (μ : ℝ) : DifferentiableAt ℝ (backorders s) μ := by
  rw [backorders_funext]
  exact (G_deriv s μ).differentiableAt

lemma strictConvex_aux (s : ℕ) (hs : 1 ≤ s) :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (backorders s) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  refine strictConvexOn_of_deriv2_pos (convex_Ioi 0) ?_ ?_
  · intro μ _
    exact (diff_backorders _ μ).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    show 0 < deriv (deriv (backorders (n + 1))) x
    rw [(deriv2_backorders n x).deriv]
    unfold poissonPmf
    have : (0 : ℝ) < x := hx
    positivity

end SMPAux

open SMPAux

lemma B2 (x : ℝ) : backorders 2 x = x - 2 + Real.exp (-x) * (2 + x) := by
  rw [backorders_eq]
  simp [G, Finset.sum_range_succ, poissonPmf]
  ring

theorem solution :
    backorders 2 1 = 3 * Real.exp (-1) - 1 ∧
    |backorders 2 1 - 0.1036| < 0.00005 ∧
    |(0.5 * backorders 2 0.5 + 0.5 * backorders 2 1.5) - 0.1486| < 0.00005 := by
  have hE1 : (0.36787944 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div, lt_div_iff₀ (Real.exp_pos _)]
    nlinarith [Real.exp_one_lt_d9]
  have hE2 : Real.exp (-1) < (0.36787945 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
    nlinarith [Real.exp_one_gt_d9]
  have h1 : backorders 2 1 = 3 * Real.exp (-1) - 1 := by
    rw [B2]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, abs_lt]; constructor <;> linarith
  · set a : ℝ := Real.exp (-1 / 2) with ha
    have ha0 : 0 < a := Real.exp_pos _
    have ha2 : a ^ 2 = Real.exp (-1) := by
      rw [ha, ← Real.exp_nat_mul]; norm_num
    have ha3 : Real.exp (-1.5 : ℝ) = a ^ 3 := by
      rw [ha, ← Real.exp_nat_mul]; norm_num
    have ha1 : Real.exp (-0.5 : ℝ) = a := by
      rw [ha]; norm_num
    have hlo : (0.6065306 : ℝ) < a := by nlinarith
    have hhi : a < (0.6065307 : ℝ) := by nlinarith
    rw [B2, B2, ha3, ha1]
    have hb1 : a ^ 3 < 0.6065307 ^ 3 := by gcongr
    have hb2 : (0.6065306 : ℝ) ^ 3 < a ^ 3 := by gcongr
    rw [abs_lt]; constructor <;> nlinarith
