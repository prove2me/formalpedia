-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.decoyConstraints
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:28:48.534981+00:00
-- url     : https://prove2.me/submissions/98222be7-4f40-45e5-a627-d009b075c6fd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)


namespace P25DcH
open QAlgorithms.Papers.Independent.Gap48.P25

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma q_nonneg {A : H →L[ℂ] H} (hA : A.IsPositive) (v : H) : 0 ≤ (inner ℂ v (A v)).re :=
  hA.re_inner_nonneg_right v

lemma q_sub (A B : H →L[ℂ] H) (v : H) :
    (inner ℂ v ((A - B) v)).re = (inner ℂ v (A v)).re - (inner ℂ v (B v)).re := by
  simp [inner_sub_right]

lemma q_one (v : H) (hv : ‖v‖ = 1) : (inner ℂ v ((1 : H →L[ℂ] H) v)).re = 1 := by
  simp only [ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, hv]; simp

lemma summ (rho : MixedSignal H) (A : H →L[ℂ] H) (hA : A.IsPositive) (hA1 : (1-A).IsPositive) :
    Summable (fun j => rho.weights.mass j * (inner ℂ (rho.vector j) (A (rho.vector j))).re) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (rho.weights.nonnegative j) (q_nonneg hA _))
    _ rho.weights.normalized.summable
  intro j
  apply mul_le_of_le_one_right (rho.weights.nonnegative j)
  have h := q_nonneg hA1 (rho.vector j)
  rw [q_sub, q_one _ (rho.unit j)] at h; linarith

end P25DcH

/-- Eq.(32), PDF p.29: common conditional states and one fixed instrument give
setting-independent f_n,g_n. Printed linearity in f_n,epsilon_n is expressed
in f_n,g_n=f_n*epsilon_n because wrong counts contain their product. Class rates
use the actual setting clock nu*w xi, converting the source conditional rates.
No claim of exact inference from finitely many settings. -/
theorem solution {X H : Type*} [Fintype X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (nu : ℝ) (hnu : 0 < nu) (w : X → ℝ)
    (hw : (∀ xi, 0 ≤ w xi) ∧ ∑ xi, w xi = 1) (p : X → PhotonLaw)
    (rho : ℕ → MixedSignal H) (M W : H →L[ℂ] H)
    (hM : M.IsPositive) (hM1 : (1-M).IsPositive) (hW : W.IsPositive)
    (hWM : (M-W).IsPositive) :
    ∃ f g e : ℕ → ℝ,
      (∀ n, f n = signalExpectation (rho n) M ∧
        g n = signalExpectation (rho n) W ∧
        0 ≤ g n ∧ g n ≤ f n ∧ f n ≤ 1 ∧ e n ∈ Set.Icc (0 : ℝ) 1 ∧ g n = f n*e n) ∧
      ∀ xi,
        Summable (decoyComponent nu w p rho M xi) ∧
        Summable (decoyWrong nu w p rho W xi) ∧
        (∑' n, decoyComponent nu w p rho M xi n) = nu*w xi*∑' n, (p xi).mass n*f n ∧
        (∑' n, decoyWrong nu w p rho W xi n) = nu*w xi*∑' n, (p xi).mass n*g n ∧
        (0 < (∑' n, decoyComponent nu w p rho M xi n) →
          (∑' n, decoyWrong nu w p rho W xi n)/(∑' n, decoyComponent nu w p rho M xi n) =
            ∑' n, (decoyComponent nu w p rho M xi n/
              (∑' k, decoyComponent nu w p rho M xi k))*e n) ∧
        (w xi = 0 → (∑' n, decoyComponent nu w p rho M xi n) = 0) := by
  have hW1 : (1 - W).IsPositive := by
    have := hM1.add hWM
    simpa using this
  set f : ℕ → ℝ := fun n => signalExpectation (rho n) M with hfdef
  set g : ℕ → ℝ := fun n => signalExpectation (rho n) W with hgdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => tsum_nonneg (fun j =>
    mul_nonneg ((rho n).weights.nonnegative j) (P25DcH.q_nonneg hM _))
  have hg0 : ∀ n, 0 ≤ g n := fun n => tsum_nonneg (fun j =>
    mul_nonneg ((rho n).weights.nonnegative j) (P25DcH.q_nonneg hW _))
  have hgf : ∀ n, g n ≤ f n := by
    intro n
    apply (P25DcH.summ (rho n) W hW hW1).tsum_le_tsum _ (P25DcH.summ (rho n) M hM hM1)
    intro j
    apply mul_le_mul_of_nonneg_left _ ((rho n).weights.nonnegative j)
    have h := P25DcH.q_nonneg hWM ((rho n).vector j)
    rw [P25DcH.q_sub] at h; linarith
  have hf1 : ∀ n, f n ≤ 1 := by
    intro n
    rw [← (rho n).weights.normalized.tsum_eq]
    apply (P25DcH.summ (rho n) M hM hM1).tsum_le_tsum _ (rho n).weights.normalized.summable
    intro j
    apply mul_le_of_le_one_right ((rho n).weights.nonnegative j)
    have h := P25DcH.q_nonneg hM1 ((rho n).vector j)
    rw [P25DcH.q_sub, P25DcH.q_one _ ((rho n).unit j)] at h; linarith
  set e : ℕ → ℝ := fun n => if f n = 0 then 0 else g n / f n with hedef
  have hgfe : ∀ n, g n = f n * e n := by
    intro n; simp only [hedef]
    split_ifs with h
    · have := hgf n; have := hg0 n; rw [h] at *; linarith
    · field_simp
  have he : ∀ n, e n ∈ Set.Icc (0:ℝ) 1 := by
    intro n; simp only [hedef]
    split_ifs with h
    · exact ⟨le_refl _, zero_le_one⟩
    · have hpos : 0 < f n := lt_of_le_of_ne (hf0 n) (Ne.symm h)
      exact ⟨div_nonneg (hg0 n) (hf0 n), (div_le_one hpos).2 (hgf n)⟩
  refine ⟨f, g, e, fun n => ⟨rfl, rfl, hg0 n, hgf n, hf1 n, he n, hgfe n⟩, fun xi => ?_⟩
  have hps := (p xi).normalized.summable
  have hpf : Summable (fun n => (p xi).mass n * f n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg ((p xi).nonnegative n) (hf0 n))
      (fun n => mul_le_of_le_one_right ((p xi).nonnegative n) (hf1 n)) hps
  have hpg : Summable (fun n => (p xi).mass n * g n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg ((p xi).nonnegative n) (hg0 n))
      (fun n => mul_le_of_le_one_right ((p xi).nonnegative n) ((hgf n).trans (hf1 n))) hps
  have hc : decoyComponent nu w p rho M xi = fun n => (nu * w xi) * ((p xi).mass n * f n) := by
    funext n; unfold decoyComponent; simp only [hfdef]; ring
  have hwr : decoyWrong nu w p rho W xi = fun n => (nu * w xi) * ((p xi).mass n * g n) := by
    funext n; unfold decoyWrong; simp only [hgdef]; ring
  have hcs : ∑' n, decoyComponent nu w p rho M xi n = nu*w xi*∑' n, (p xi).mass n*f n := by
    rw [hc, tsum_mul_left]
  have hws : ∑' n, decoyWrong nu w p rho W xi n = nu*w xi*∑' n, (p xi).mass n*g n := by
    rw [hwr, tsum_mul_left]
  refine ⟨by rw [hc]; exact hpf.mul_left _, by rw [hwr]; exact hpg.mul_left _, hcs, hws,
    fun hT => ?_, fun h0 => ?_⟩
  · have : (fun n => decoyComponent nu w p rho M xi n / (∑' k, decoyComponent nu w p rho M xi k) * e n) =
        fun n => decoyWrong nu w p rho W xi n / (∑' k, decoyComponent nu w p rho M xi k) := by
      funext n
      rw [hwr, hc]; simp only; rw [hgfe n]; ring
    rw [this, tsum_div_const]
  · rw [hcs, h0]; ring




