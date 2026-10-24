-- Prove2me | solution 1 for UniversalBarrier.NSC.f0_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:36:06.037465+00:00
-- url     : https://prove2.me/submissions/86a9f65e-3fec-4e2f-a522-b0be4e202bdf

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC.PolynomialProof

/-- The first auxiliary polynomial in §4.1.7, written with k = m + 2. -/
def f1 (m : ℕ) (x : ℝ) : ℝ :=
  2 * (2 * ((m : ℝ)+2)+1) * x^(m+3) - 2 * ((m : ℝ)+3) * x^(m+2)
    - ((m : ℝ)+2)*((m : ℝ)+3)*((m : ℝ)+4)*x^2
    + 2*((m : ℝ)+3)*(((m : ℝ)+2)^2+((m : ℝ)+2)-1)*x
    - (((m : ℝ)+2)^3+((m : ℝ)+2)^2-2)

/-- The second auxiliary polynomial in §4.1.7. -/
def f2 (m : ℕ) (x : ℝ) : ℝ :=
  (2*((m : ℝ)+2)+1)*x^(m+2) - ((m : ℝ)+2)*x^(m+1)
    - ((m : ℝ)+2)*((m : ℝ)+4)*x + (((m : ℝ)+2)^2+((m : ℝ)+2)-1)

lemma hasDerivAt_f2 (m : ℕ) (x : ℝ) :
    HasDerivAt (f2 m)
      (((m : ℝ)+2) * x^m * ((2*((m : ℝ)+2)+1)*x-((m : ℝ)+1))
        - ((m : ℝ)+2)*((m : ℝ)+4)) x := by
  have h := ((((hasDerivAt_pow (m+2) x).const_mul (2*((m : ℝ)+2)+1)).sub
    ((hasDerivAt_pow (m+1) x).const_mul ((m : ℝ)+2))).sub
    ((hasDerivAt_id x).const_mul (((m : ℝ)+2)*((m : ℝ)+4)))).add_const
      (((m : ℝ)+2)^2+((m : ℝ)+2)-1)
  convert! h using 1
  norm_num [f2, Nat.add_sub_assoc, pow_succ]
  ring

lemma hasDerivAt_f1 (m : ℕ) (x : ℝ) :
    HasDerivAt (f1 m) (2*((m : ℝ)+3)*f2 m x) x := by
  have h := (((((hasDerivAt_pow (m+3) x).const_mul (2*(2*((m : ℝ)+2)+1))).sub
    ((hasDerivAt_pow (m+2) x).const_mul (2*((m : ℝ)+3)))).sub
    ((hasDerivAt_pow 2 x).const_mul (((m : ℝ)+2)*((m : ℝ)+3)*((m : ℝ)+4)))).add
    ((hasDerivAt_id x).const_mul (2*((m : ℝ)+3)*(((m : ℝ)+2)^2+((m : ℝ)+2)-1)))).sub_const
      (((m : ℝ)+2)^3+((m : ℝ)+2)^2-2)
  convert! h using 1
  norm_num [f1, f2, Nat.add_sub_assoc, pow_succ]
  ring

lemma hasDerivAt_f0 (m : ℕ) (x : ℝ) :
    HasDerivAt (f0 (m+2)) (((m : ℝ)+2)*x^(m+1)*f1 m x) x := by
  let k : ℝ := (m : ℝ)+2
  have hA := (hasDerivAt_pow (m+2) x).sub_const 1
  have hB := (hasDerivAt_pow (m+3) x).sub_const 1
  have hC := (hasDerivAt_pow (m+4) x).sub_const 1
  have h := ((hA.const_mul k).mul
    (((hC.const_mul (k*(k+1))).sub (hB.const_mul (2*k*(k+2)))).add
      (hA.const_mul ((k+1)*(k+2))))).sub
    ((((hB.const_mul k).sub (hA.const_mul (k+1))).pow 2).const_mul (k+1))
  convert! h using 1
  all_goals try funext y
  all_goals norm_num [f0, f1, k, Nat.add_assoc, Nat.add_sub_assoc, pow_succ]
  all_goals ring

lemma nonneg_from_derivative {f d : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (d x) x)
    (h1 : f 1 = 0) (hd : ∀ x, 1 ≤ x → 0 ≤ d x) : ∀ x, 1 ≤ x → 0 ≤ f x := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hm : MonotoneOn f (Set.Ici 1) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici 1) hc.continuousOn (fun x _ => (hf x).hasDerivWithinAt)
    (fun x hx => hd x (interior_subset hx))
  intro x hx
  simpa only [h1] using hm (show (1 : ℝ) ∈ Set.Ici 1 from by simp) hx hx

lemma f2_nonneg (m : ℕ) : ∀ x : ℝ, 1 ≤ x → 0 ≤ f2 m x := by
  apply nonneg_from_derivative (hasDerivAt_f2 m)
  · simp only [f2, one_pow]; ring
  · intro x hx
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hp : 1 ≤ x^m := one_le_pow₀ hx
    have hl : (m : ℝ)+4 ≤ (2*((m : ℝ)+2)+1)*x-((m : ℝ)+1) := by nlinarith
    have hprod := mul_le_mul hp hl (by positivity : (0 : ℝ) ≤ (m : ℝ)+4) (by positivity : 0 ≤ x^m)
    have hc := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ (m : ℝ)+2)
    nlinarith

lemma f1_nonneg (m : ℕ) : ∀ x : ℝ, 1 ≤ x → 0 ≤ f1 m x := by
  apply nonneg_from_derivative (hasDerivAt_f1 m)
  · simp only [f1, one_pow]; ring
  · intro x hx
    exact mul_nonneg (by positivity) (f2_nonneg m x hx)

lemma f0_nonneg_succ (m : ℕ) : ∀ x : ℝ, 1 ≤ x → 0 ≤ f0 (m+2) x := by
  apply nonneg_from_derivative (hasDerivAt_f0 m)
  · simp [f0]
  · intro x hx
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      (f1_nonneg m x hx)

end UniversalBarrier.NSC.PolynomialProof

open UniversalBarrier.NSC

theorem solution (k : ℕ) (hk : 2 ≤ k) (γ : ℝ) (hγ : 1 ≤ γ) : 0 ≤ f0 k γ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm 2] using PolynomialProof.f0_nonneg_succ m γ hγ
