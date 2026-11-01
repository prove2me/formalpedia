-- Prove2me | solution 1 for SingCtrlLevy.Barrier.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:36:14.323075+00:00
-- url     : https://prove2.me/submissions/d5d55977-70f2-42aa-bb2b-723358483e85

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

open SingCtrlLevy.Barrier

namespace SingCtrlLevyLemma12Aux

/-- FTC for the right derivative of a convex function on `ℝ`. -/
lemma integral_rd {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (a b : ℝ) :
    ∫ u in a..b, rd f u = f b - f a := by
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hmono : Monotone (rd f) := fun x y h =>
    hf.monotoneOn_rightDeriv (by simp) (by simp) h
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont.continuousOn
  · intro x _
    exact hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  · exact hmono.intervalIntegrable

lemma inner_eq {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (ε x z : ℝ) :
    ∫ y in (-ε)..0, rd f (x + y + z) = f (x + z) - f (x + z - ε) := by
  have h1 : (fun y => rd f (x + y + z)) = fun y => rd f (y + (x + z)) := by
    funext y; congr 1; ring
  rw [h1, intervalIntegral.integral_comp_add_right (fun u => rd f u) (x + z), integral_rd hf]
  congr 1
  · congr 1; ring
  · congr 1; ring

lemma pow_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    (a + b) ^ N ≤ 2 ^ N * (a ^ N + b ^ N) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ N ≤ (2 * b) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * b ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (a ^ N + b ^ N) := by
        have : 0 ≤ a ^ N := pow_nonneg ha N
        have : (0:ℝ) ≤ 2 ^ N := by positivity
        nlinarith
  · calc (a + b) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (a ^ N + b ^ N) := by
        have : 0 ≤ b ^ N := pow_nonneg hb N
        have : (0:ℝ) ≤ 2 ^ N := by positivity
        nlinarith

end SingCtrlLevyLemma12Aux

open SingCtrlLevyLemma12Aux in
theorem solution (f : ℝ → ℝ) (q C : ℝ) (hA1 : Assumption1 f C q) (b ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 2 (fEps f b ε) ∧
      ∃ k₁ k₂ : ℝ, ∃ N : ℕ, ∀ x, |iteratedDeriv 2 (fEps f b ε) x| ≤ k₁ + k₂ * |x| ^ N := by
  obtain ⟨hf, ⟨k₁, k₂, N, hgrowth⟩, -, -⟩ := hA1
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  -- primitive of `f`
  set Φ : ℝ → ℝ := fun u => ∫ t in (0:ℝ)..u, f t with hΦ
  have hΦd : ∀ u, HasDerivAt Φ (f u) u := fun u =>
    (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  -- closed form of `f^{(ε)'}`
  set h : ℝ → ℝ := fun x => 1 / ε ^ 2 * (Φ x - 2 * Φ (x - ε) + Φ (x - 2 * ε)) with hh
  set k : ℝ → ℝ := fun x => 1 / ε ^ 2 * (f x - 2 * f (x - ε) + f (x - 2 * ε)) with hk
  have hkc : Continuous k := by
    simp only [hk]; fun_prop
  have hhd : ∀ x, HasDerivAt h (k x) x := by
    intro x
    have e1 : HasDerivAt (fun x => Φ (x - ε)) (f (x - ε)) x := by
      simpa using (hΦd (x - ε)).comp_sub_const x ε
    have e2 : HasDerivAt (fun x => Φ (x - 2 * ε)) (f (x - 2 * ε)) x := by
      simpa using (hΦd (x - 2 * ε)).comp_sub_const x (2 * ε)
    have := (((hΦd x).sub (e1.const_mul 2)).add e2).const_mul (1 / ε ^ 2)
    simpa [hh, hk] using this
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hhd x).continuousAt
  have hE : fEpsDeriv f ε = h := by
    funext x
    simp only [fEpsDeriv]
    simp_rw [inner_eq hf ε x]
    have hint : ∫ z in (-ε)..0, (f (x + z) - f (x + z - ε)) =
        (Φ x - Φ (x - ε)) - (Φ (x - ε) - Φ (x - 2 * ε)) := by
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun z => Φ (x + z) - Φ (x + z - ε)) ?_ ?_).trans ?_
      · intro z _
        have a1 : HasDerivAt (fun z => Φ (x + z)) (f (x + z)) z := by
          simpa using (hΦd (x + z)).comp_const_add x z
        have a2 : HasDerivAt (fun z => Φ (x + z - ε)) (f (x + z - ε)) z := by
          have e : x - ε + z = x + z - ε := by ring
          have := (e ▸ hΦd (x + z - ε)).comp_const_add (x - ε) z
          have e' : (fun z => Φ (x - ε + z)) = fun z => Φ (x + z - ε) := by
            funext z; congr 1; ring
          rw [e', e] at this
          exact this
        exact a1.sub a2
      · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
      · show Φ (x + 0) - Φ (x + 0 - ε) - (Φ (x + -ε) - Φ (x + -ε - ε)) = _
        rw [show x + 0 = x by ring, show x + -ε = x - ε by ring,
          show x - ε - ε = x - 2 * ε by ring]
    rw [hint]
    simp only [hh]
    ring
  have hF : fEps f b ε = fun x => f b + ∫ y in b..x, h y := by
    funext x
    simp only [fEps, hE]
  have hFd : ∀ x, HasDerivAt (fEps f b ε) (h x) x := by
    intro x
    rw [hF]
    exact ((hhc.integral_hasStrictDerivAt b x).hasDerivAt).const_add (f b)
  have hderivF : deriv (fEps f b ε) = h := funext fun x => (hFd x).deriv
  have hderivh : deriv h = k := funext fun x => (hhd x).deriv
  have hdiffF : Differentiable ℝ (fEps f b ε) := fun x => (hFd x).differentiableAt
  have hdiffh : Differentiable ℝ h := fun x => (hhd x).differentiableAt
  refine ⟨?_, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨hdiffF, by simp, ?_⟩
    rw [hderivF, contDiff_one_iff_deriv]
    exact ⟨hdiffh, by rw [hderivh]; exact hkc⟩
  · have h2 : iteratedDeriv 2 (fEps f b ε) = k := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hderivF, hderivh]
    rw [h2]
    -- growth bound
    set K := |k₂| with hK
    have hg : ∀ y, |f y| ≤ |k₁| + K * |y| ^ N := by
      intro y
      have := hgrowth y
      have : k₂ * |y| ^ N ≤ |k₂| * |y| ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self k₂) (pow_nonneg (abs_nonneg y) N)
      linarith [le_abs_self k₁]
    have hpoly : ∀ x y, |y - x| ≤ 2 * ε →
        |f y| ≤ |k₁| + K * (2 ^ N * (|x| ^ N + (2 * ε) ^ N)) := by
      intro x y hy
      have hy' : |y| ≤ |x| + 2 * ε := by
        have := abs_sub_abs_le_abs_sub y x
        linarith
      have hpow : |y| ^ N ≤ 2 ^ N * (|x| ^ N + (2 * ε) ^ N) :=
        (pow_le_pow_left₀ (abs_nonneg y) hy' N).trans
          (pow_add_le _ _ (abs_nonneg x) (by positivity) N)
      have hK0 : 0 ≤ K := abs_nonneg _
      calc |f y| ≤ |k₁| + K * |y| ^ N := hg y
        _ ≤ |k₁| + K * (2 ^ N * (|x| ^ N + (2 * ε) ^ N)) := by
          gcongr
    refine ⟨4 / ε ^ 2 * (|k₁| + K * 2 ^ N * (2 * ε) ^ N), 4 / ε ^ 2 * (K * 2 ^ N), N, ?_⟩
    intro x
    have b0 := hpoly x x (by simp; positivity)
    have b1 := hpoly x (x - ε) (by
      rw [show x - ε - x = -ε by ring, abs_neg, abs_of_pos hε]; linarith)
    have b2 := hpoly x (x - 2 * ε) (by
      rw [show x - 2 * ε - x = -(2 * ε) by ring, abs_neg, abs_of_pos (by linarith)])
    have hε2 : 0 < ε ^ 2 := by positivity
    simp only [hk]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / ε ^ 2)]
    have htri : |f x - 2 * f (x - ε) + f (x - 2 * ε)|
        ≤ |f x| + 2 * |f (x - ε)| + |f (x - 2 * ε)| := by
      have h3 := abs_add_le (f x + -(2 * f (x - ε))) (f (x - 2 * ε))
      have h4 := abs_add_le (f x) (-(2 * f (x - ε)))
      have h2' : |2 * f (x - ε)| = 2 * |f (x - ε)| := by
        rw [abs_mul]; norm_num
      rw [abs_neg, h2'] at h4
      rw [sub_eq_add_neg]
      linarith
    have hsum : |f x| + 2 * |f (x - ε)| + |f (x - 2 * ε)|
        ≤ 4 * (|k₁| + K * (2 ^ N * (|x| ^ N + (2 * ε) ^ N))) := by linarith
    calc 1 / ε ^ 2 * |f x - 2 * f (x - ε) + f (x - 2 * ε)|
        ≤ 1 / ε ^ 2 * (4 * (|k₁| + K * (2 ^ N * (|x| ^ N + (2 * ε) ^ N)))) := by
          gcongr; exact htri.trans hsum
      _ = 4 / ε ^ 2 * (|k₁| + K * 2 ^ N * (2 * ε) ^ N) + 4 / ε ^ 2 * (K * 2 ^ N) * |x| ^ N := by
          ring
