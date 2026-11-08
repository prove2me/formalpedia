-- Prove2me | solution 1 for RegretBandits.Adversarial.exp3P_regret_general
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:20:14.454166+00:00
-- url     : https://prove2.me/submissions/0f46ac95-0b4c-4fbc-a868-d72b4682fd6e

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P
import Theorems.Thm_RegretBandits_Adversarial_biased_gain_estimate_bound

open MeasureTheory
open RegretBandits.Adversarial

namespace Exp3PGenAux

lemma gibbs_pos {K : ℕ} (c : ℝ) (x : Fin K → ℝ) (i : Fin K) : 0 < gibbs c x i := by
  unfold gibbs
  have : 0 < ∑ k, Real.exp (c * x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  positivity

lemma gibbs_sum {K : ℕ} (hK : 0 < K) (c : ℝ) (x : Fin K → ℝ) : ∑ i, gibbs c x i = 1 := by
  unfold gibbs
  have : 0 < ∑ k, Real.exp (c * x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  rw [← Finset.sum_div, div_self this.ne']

/-- One step of the exponential-weights analysis (eqs. (3.14)–(3.15)). -/
lemma step_ineq {K : ℕ} (hK : 0 < K) (x y : Fin K → ℝ) (β γ η : ℝ) (hη : 0 < η)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, η * y i ≤ 1)
    (hpy : ∀ i, ((1 - γ) * gibbs η x i + γ / K) * y i ≤ 1 + β) :
    (1 - γ) / η * (Real.log (∑ i, Real.exp (η * (x i + y i))) -
        Real.log (∑ i, Real.exp (η * x i))) - (1 + β) * η * ∑ i, y i ≤
      ∑ i, ((1 - γ) * gibbs η x i + γ / K) * y i := by
  set W0 := ∑ i, Real.exp (η * x i) with hW0
  have hW0pos : 0 < W0 := Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  set w := gibbs η x with hw
  have hwdef : ∀ i, w i = Real.exp (η * x i) / W0 := fun i => rfl
  have hw0 : ∀ i, 0 < w i := fun i => gibbs_pos η x i
  have hwsum : ∑ i, w i = 1 := gibbs_sum hK η x
  set S := ∑ i, w i * Real.exp (η * y i) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => mul_pos (hw0 i) (Real.exp_pos _))
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hW1 : ∑ i, Real.exp (η * (x i + y i)) = W0 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hwdef, mul_add, Real.exp_add]
    field_simp
  have hlog : Real.log (∑ i, Real.exp (η * (x i + y i))) - Real.log W0 = Real.log S := by
    rw [hW1, Real.log_mul hW0pos.ne' hSpos.ne']; ring
  rw [hlog]
  have hexp : ∀ i, Real.exp (η * y i) ≤ 1 + η * y i + (η * y i) ^ 2 := by
    intro i
    have h1 : |η * y i| ≤ 1 := by
      rw [abs_le]; constructor
      · have := mul_nonneg hη.le (hy0 i); linarith
      · exact hy1 i
    have := Real.abs_exp_sub_one_sub_id_le h1
    rw [abs_le] at this
    linarith [this.2]
  have hS1 : Real.log S ≤ ∑ i, w i * (η * y i + (η * y i) ^ 2) := by
    have := Real.log_le_sub_one_of_pos hSpos
    have h2 : S ≤ ∑ i, w i * (1 + η * y i + (η * y i) ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hexp i) (hw0 i).le)
    have h3 : ∑ i, w i * (1 + η * y i + (η * y i) ^ 2) =
        ∑ i, w i + ∑ i, w i * (η * y i + (η * y i) ^ 2) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have hc : 0 ≤ (1 - γ) / η := div_nonneg (by linarith) hη.le
  have h4 : (1 - γ) / η * Real.log S ≤
      ∑ i, ((1 - γ) * w i * y i + η * ((1 - γ) * w i * y i) * y i) := by
    calc (1 - γ) / η * Real.log S ≤ (1 - γ) / η * ∑ i, w i * (η * y i + (η * y i) ^ 2) :=
          mul_le_mul_of_nonneg_left hS1 hc
      _ = ∑ i, ((1 - γ) * w i * y i + η * ((1 - γ) * w i * y i) * y i) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
          field_simp
  have h5 : ∀ i, (1 - γ) * w i * y i + η * ((1 - γ) * w i * y i) * y i ≤
      ((1 - γ) * w i + γ / K) * y i + (1 + β) * η * y i := by
    intro i
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hA : (1 - γ) * w i * y i ≤ ((1 - γ) * w i + γ / K) * y i := by
      have : 0 ≤ γ / K * y i := mul_nonneg (div_nonneg hγ0 hKr.le) (hy0 i)
      nlinarith
    have hB : η * ((1 - γ) * w i * y i) * y i ≤ (1 + β) * η * y i := by
      have h6 := hA.trans (hpy i)
      have h7 : 0 ≤ η * y i := mul_nonneg hη.le (hy0 i)
      calc η * ((1 - γ) * w i * y i) * y i = ((1 - γ) * w i * y i) * (η * y i) := by ring
        _ ≤ (1 + β) * (η * y i) := mul_le_mul_of_nonneg_right h6 h7
        _ = (1 + β) * η * y i := by ring
    linarith
  have h8 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h5 i)
  have h9 : ∑ i, (((1 - γ) * w i + γ / K) * y i + (1 + β) * η * y i) =
      ∑ i, ((1 - γ) * w i + γ / K) * y i + (1 + β) * η * ∑ i, y i := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h9] at h8
  linarith


section path
variable {K : ℕ} (β γ η : ℝ) (g : Adversary K)

lemma prob_succ (t : ℕ) (h : ℕ → Fin K) :
    exp3PProb β γ η g (t + 1) h = exp3PMix γ η (exp3PCumGain β γ η g t h) := by
  simp [exp3PProb]

lemma mix_ge_unif (hK : 0 < K) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (G : Fin K → ℝ) (i : Fin K) :
    γ / K ≤ exp3PMix γ η G i := by
  unfold exp3PMix
  have := gibbs_pos η G i
  have : 0 ≤ (1 - γ) * gibbs η G i := mul_nonneg (by linarith) this.le
  linarith

lemma mix_pos (hK : 0 < K) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (G : Fin K → ℝ) (i : Fin K) :
    0 < exp3PMix γ η G i := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  exact lt_of_lt_of_le (div_pos hγ0 hKr) (mix_ge_unif γ η hK hγ0 hγ1 G i)

lemma mix_sum (hK : 0 < K) (G : Fin K → ℝ) : ∑ i, exp3PMix γ η G i = 1 := by
  unfold exp3PMix
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, gibbs_sum hK]
  simp
  field_simp
  ring

lemma cum_agree (t : ℕ) (h h' : ℕ → Fin K) (hh : ∀ s, 1 ≤ s → s ≤ t → h s = h' s) :
    exp3PCumGain β γ η g t h = exp3PCumGain β γ η g t h' := by
  induction t with
  | zero => funext i; rfl
  | succ t ih =>
    have ih' := ih (fun s h1 h2 => hh s h1 (by omega))
    have hv : g.val (t + 1) h = g.val (t + 1) h' :=
      g.nonanticipating _ _ _ (fun s h1 h2 => hh s h1 (by omega))
    have hl : h (t + 1) = h' (t + 1) := hh _ (by omega) le_rfl
    funext i
    show exp3PCumGain β γ η g t h i +
        (g.val (t + 1) h i * (if h (t + 1) = i then 1 else 0) + β) /
          exp3PMix γ η (exp3PCumGain β γ η g t h) i =
      exp3PCumGain β γ η g t h' i +
        (g.val (t + 1) h' i * (if h' (t + 1) = i then 1 else 0) + β) /
          exp3PMix γ η (exp3PCumGain β γ η g t h') i
    rw [ih', hv, hl]

lemma isForecasterRule (hK : 0 < K) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    IsForecasterRule (exp3PProb β γ η g) := by
  refine ⟨fun t h i => (mix_pos γ η hK hγ0 hγ1 _ i).le, fun t h => mix_sum γ η hK _, ?_⟩
  intro t h h' hh
  unfold exp3PProb
  rw [cum_agree β γ η g (t - 1) h h' (fun s h1 h2 => hh s h1 (by omega))]

/-- The estimate `g̃_{i,t}`. -/
noncomputable def est (t : ℕ) (h : ℕ → Fin K) (i : Fin K) : ℝ :=
  (g.val t h i * (if h t = i then 1 else 0) + β) / exp3PProb β γ η g t h i

lemma sum_est (n : ℕ) (h : ℕ → Fin K) (i : Fin K) :
    ∑ t ∈ Finset.Icc 1 n, est β γ η g t h i = exp3PCumGain β γ η g n h i := by
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    unfold est
    rw [prob_succ]
    rfl

lemma est_nonneg (hK : 0 < K) (hβ : 0 ≤ β) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (t : ℕ)
    (h : ℕ → Fin K) (i : Fin K) : 0 ≤ est β γ η g t h i := by
  unfold est exp3PProb
  have := mix_pos γ η hK hγ0 hγ1 (exp3PCumGain β γ η g (t - 1) h) i
  have h1 := (g.val_mem t h i).1
  have : 0 ≤ g.val t h i * (if h t = i then 1 else 0) := by
    split_ifs <;> simp [h1]
  positivity

lemma p_est_le (hK : 0 < K) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (t : ℕ)
    (h : ℕ → Fin K) (i : Fin K) :
    exp3PProb β γ η g t h i * est β γ η g t h i ≤ 1 + β := by
  unfold est
  have hp : 0 < exp3PProb β γ η g t h i := mix_pos γ η hK hγ0 hγ1 _ i
  rw [mul_div_cancel₀ _ hp.ne']
  have h1 := (g.val_mem t h i).2
  have h0 := (g.val_mem t h i).1
  have : g.val t h i * (if h t = i then 1 else 0) ≤ 1 := by
    split_ifs <;> simp [h1]
  linarith

lemma eta_est_le (hK : 0 < K) (hβ : 0 ≤ β) (hη : 0 < η) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hβηγ : (1 + β) * K * η ≤ γ) (t : ℕ) (h : ℕ → Fin K) (i : Fin K) :
    η * est β γ η g t h i ≤ 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hp : γ / K ≤ exp3PProb β γ η g t h i := mix_ge_unif γ η hK hγ0 hγ1 _ i
  have hp0 : 0 < exp3PProb β γ η g t h i := mix_pos γ η hK hγ0 hγ1 _ i
  have h1 := p_est_le β γ η g hK hγ0 hγ1 t h i
  have h2 := est_nonneg β γ η g hK hβ hγ0 hγ1 t h i
  -- (γ/K) * est ≤ 1 + β
  have h3 : γ / K * est β γ η g t h i ≤ 1 + β :=
    le_trans (mul_le_mul_of_nonneg_right hp h2) h1
  have h4 : γ * est β γ η g t h i ≤ (1 + β) * K := by
    have := mul_le_mul_of_nonneg_left h3 hKr.le
    rw [show (K : ℝ) * (γ / K * est β γ η g t h i) = γ * est β γ η g t h i by field_simp] at this
    linarith
  -- η * est * γ ≤ (1+β) K η ≤ γ
  have h5 : η * est β γ η g t h i * γ ≤ 1 * γ := by
    have := mul_le_mul_of_nonneg_left h4 hη.le
    nlinarith
  exact le_of_mul_le_mul_right h5 hγ0

lemma sum_p_est (hK : 0 < K) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (t : ℕ) (h : ℕ → Fin K) :
    ∑ i, exp3PProb β γ η g t h i * est β γ η g t h i = g.val t h (h t) + β * K := by
  have : ∀ i, exp3PProb β γ η g t h i * est β γ η g t h i =
      g.val t h i * (if h t = i then 1 else 0) + β := by
    intro i
    unfold est
    exact mul_div_cancel₀ _ (mix_pos γ η hK hγ0 hγ1 _ i).ne'
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]
  ring

lemma cum_succ_est (t : ℕ) (h : ℕ → Fin K) (i : Fin K) :
    exp3PCumGain β γ η g (t + 1) h i = exp3PCumGain β γ η g t h i + est β γ η g (t + 1) h i := by
  unfold est; rw [prob_succ]; rfl

lemma summed (hK : 0 < K) (hβ : 0 ≤ β) (hη : 0 < η) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hβηγ : (1 + β) * K * η ≤ γ) (n : ℕ) (h : ℕ → Fin K) :
    (1 - γ) / η * (Real.log (∑ i, Real.exp (η * exp3PCumGain β γ η g n h i)) - Real.log K) -
        (1 + β) * η * ∑ i, exp3PCumGain β γ η g n h i ≤
      ∑ t ∈ Finset.Icc 1 n, ∑ i, exp3PProb β γ η g t h i * est β γ η g t h i := by
  induction n with
  | zero =>
    have : ∀ i, exp3PCumGain β γ η g 0 h i = 0 := fun i => rfl
    simp [this]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hst := step_ineq hK (exp3PCumGain β γ η g n h) (est β γ η g (n + 1) h) β γ η hη
      hγ0.le (by linarith) (fun i => est_nonneg β γ η g hK hβ hγ0 hγ1 _ h i)
      (fun i => eta_est_le β γ η g hK hβ hη hγ0 hγ1 hβηγ _ h i)
      (fun i => by
        have := p_est_le β γ η g hK hγ0 hγ1 (n + 1) h i
        rw [prob_succ] at this
        exact this)
    have hp : ∀ i, exp3PProb β γ η g (n + 1) h i =
        (1 - γ) * gibbs η (exp3PCumGain β γ η g n h) i + γ / K := by
      intro i; rw [prob_succ]; rfl
    simp only [hp]
    have hc : ∀ i, exp3PCumGain β γ η g (n + 1) h i =
        exp3PCumGain β γ η g n h i + est β γ η g (n + 1) h i := cum_succ_est β γ η g n h
    simp only [hc, Finset.sum_add_distrib]
    have e : (1 - γ) / η * (Real.log (∑ i, Real.exp (η * (exp3PCumGain β γ η g n h i +
        est β γ η g (n + 1) h i))) - Real.log K) =
        (1 - γ) / η * (Real.log (∑ i, Real.exp (η * (exp3PCumGain β γ η g n h i +
        est β γ η g (n + 1) h i))) - Real.log (∑ i, Real.exp (η * exp3PCumGain β γ η g n h i))) +
        (1 - γ) / η * (Real.log (∑ i, Real.exp (η * exp3PCumGain β γ η g n h i)) - Real.log K) := by
      ring
    rw [e]
    linarith [hst, ih]

lemma pathwise (hK : 0 < K) (hβ : 0 ≤ β) (hη : 0 < η) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hβηγ : (1 + β) * K * η ≤ γ) (n : ℕ) (h : ℕ → Fin K) (B : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ k, ∑ t ∈ Finset.Icc 1 n, g.val t h k ≤ ∑ t ∈ Finset.Icc 1 n, est β γ η g t h k + B)
    (k : Fin K) :
    ∑ t ∈ Finset.Icc 1 n, g.val t h k - ∑ t ∈ Finset.Icc 1 n, g.val t h (h t) ≤
      β * n * K + γ * n + (1 + β) * η * K * n + B + Real.log K / η := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr1
  have hsumP : ∑ t ∈ Finset.Icc 1 n, ∑ i, exp3PProb β γ η g t h i * est β γ η g t h i =
      ∑ t ∈ Finset.Icc 1 n, g.val t h (h t) + β * n * K := by
    rw [Finset.sum_congr rfl (fun t _ => sum_p_est β γ η g hK hγ0 hγ1 t h),
      Finset.sum_add_distrib]
    simp
    ring
  have hsum := summed β γ η g hK hβ hη hγ0 hγ1 hβηγ n h
  set G := exp3PCumGain β γ η g n h with hG
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ G ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hW : η * G j0 ≤ Real.log (∑ i, Real.exp (η * G i)) := by
    have h1 : Real.exp (η * G j0) ≤ ∑ i, Real.exp (η * G i) :=
      Finset.single_le_sum (f := fun i => Real.exp (η * G i)) (fun i _ => (Real.exp_pos _).le)
        (Finset.mem_univ j0)
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hsumG : ∑ i, G i ≤ K * G j0 := by
    have := Finset.sum_le_sum (fun i (hi : i ∈ Finset.univ) => hj0 i hi)
    simpa using this
  have hc1 : 0 ≤ (1 - γ) / η := div_nonneg (by linarith) hη.le
  have hA : (1 - γ) / η * (η * G j0 - Real.log K) ≤
      (1 - γ) / η * (Real.log (∑ i, Real.exp (η * G i)) - Real.log K) :=
    mul_le_mul_of_nonneg_left (by linarith) hc1
  have hA' : (1 - γ) / η * (η * G j0 - Real.log K) = (1 - γ) * G j0 - (1 - γ) * (Real.log K / η) := by
    field_simp
  have hB2 : (1 + β) * η * ∑ i, G i ≤ (1 + β) * η * (K * G j0) :=
    mul_le_mul_of_nonneg_left hsumG (by positivity)
  set A := ∑ t ∈ Finset.Icc 1 n, g.val t h k with hAdef
  have hAn : A ≤ n := by
    calc A ≤ ∑ t ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (g.val_mem _ _ _).2)
      _ = n := by simp
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun t _ => (g.val_mem _ _ _).1)
  have hGk : A - B ≤ G j0 := by
    have := hgood k
    rw [sum_est] at this
    have := hj0 k (Finset.mem_univ _)
    linarith
  set c := 1 - γ - (1 + β) * η * K with hc
  have hc0 : 0 ≤ c := by
    have : (1 + β) * η * K = (1 + β) * K * η := by ring
    rw [hc, this]; linarith
  have hcle : c ≤ 1 := by
    have : 0 ≤ (1 + β) * η * K := by positivity
    rw [hc]; linarith
  have hcG : c * (A - B) ≤ c * G j0 := mul_le_mul_of_nonneg_left hGk hc0
  have hlogη : (1 - γ) * (Real.log K / η) ≤ Real.log K / η := by
    have : 0 ≤ Real.log K / η := div_nonneg hlogK hη.le
    nlinarith
  have h1c : (1 - c) * A ≤ (1 - c) * n := mul_le_mul_of_nonneg_left hAn (by linarith)
  have hcB : c * B ≤ B := by nlinarith
  have hexp : (1 - c) * n = γ * n + (1 + β) * η * K * n := by rw [hc]; ring
  have hcGe : c * G j0 = (1 - γ) * G j0 - (1 + β) * η * (K * G j0) := by rw [hc]; ring
  nlinarith [hsumP, hsum, hA, hA', hB2, hcG, hlogη, h1c, hcB, hexp, hcGe]

end path

lemma meas_dep {K : ℕ} (hK : 0 < K) {Ω : Type*} [MeasurableSpace Ω] (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (n : ℕ) (F : (ℕ → Fin K) → ℝ)
    (hF : ∀ h h' : ℕ → Fin K, (∀ s, s ≤ n → h s = h' s) → F h = F h') :
    Measurable (fun ω => F (fun s => I s ω)) := by
  let d : Fin K := ⟨0, hK⟩
  let ext : (Fin (n + 1) → Fin K) → (ℕ → Fin K) :=
    fun r s => if hs : s < n + 1 then r ⟨s, hs⟩ else d
  have heq : (fun ω => F (fun s => I s ω)) =
      (fun r => F (ext r)) ∘ (fun ω => (fun s : Fin (n + 1) => I s ω)) := by
    funext ω
    simp only [Function.comp]
    apply hF
    intro s hs
    have : s < n + 1 := by omega
    show I s ω = (if hs : s < n + 1 then I s ω else d)
    rw [dif_pos this]
  rw [heq]
  exact (measurable_of_countable _).comp (measurable_pi_lambda _ (fun s => hI s))

end Exp3PGenAux

open Exp3PGenAux in
theorem solution {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    (β γ η δ : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hη : 0 < η) (hγ : γ ≤ 1 / 2)
    (hβηγ : (1 + β) * K * η ≤ γ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K) (hI : IsRun P (exp3PProb β γ η g) I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤
        β * n * K + γ * n + (1 + β) * η * K * n + Real.log (K * δ⁻¹) / β + Real.log K / η} := by
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKr2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hγ0 : 0 < γ := by
    have : 0 < (1 + β) * K * η := by positivity
    linarith
  have hrule := isForecasterRule β γ η g hK0 hγ0 hγ
  have hδK0 : 0 < δ / K := div_pos hδ0 hKr
  have hδK1 : δ / K < 1 := by
    rw [div_lt_one hKr]; linarith
  have hlogeq : Real.log (δ / K)⁻¹ = Real.log (K * δ⁻¹) := by
    rw [inv_div, div_eq_mul_inv]
  have hB : 0 ≤ Real.log (K * δ⁻¹) / β := by
    apply div_nonneg _ hβ0.le
    apply Real.log_nonneg
    have : 1 < δ⁻¹ := one_lt_inv_iff₀.2 ⟨hδ0, hδ1⟩
    nlinarith
  set B := Real.log (K * δ⁻¹) / β with hBdef
  let E : Fin K → Set Ω := fun k => {ω | ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) k ≤
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) k * (if I t ω = k then 1 else 0) + β) /
              exp3PProb β γ η g t (fun s => I s ω) k + B}
  have hEprob : ∀ k, ENNReal.ofReal (1 - δ / K) ≤ P (E k) := by
    intro k
    have := RegretBandits.Adversarial.biased_gain_estimate_bound hK n g (exp3PProb β γ η g) hrule k
      (fun t h => mix_pos γ η hK0 hγ0 hγ _ k) β (δ / K) hβ0 hβ1 hδK0 hδK1 P I hI
    rw [hlogeq] at this
    exact this
  have hEmeas : ∀ k, MeasurableSet (E k) := by
    intro k
    apply measurableSet_le
    · exact meas_dep hK0 I hI.1 n (fun h => ∑ t ∈ Finset.Icc 1 n, g.val t h k) (by
        intro h h' hh
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [g.nonanticipating t h h' (fun s h1 h2 => hh s (by simp at ht; omega))])
    · exact (meas_dep hK0 I hI.1 n (fun h => ∑ t ∈ Finset.Icc 1 n,
            (g.val t h k * (if h t = k then 1 else 0) + β) / exp3PProb β γ η g t h k) (by
        intro h h' hh
        refine Finset.sum_congr rfl (fun t ht => ?_)
        have ht' : t ≤ n := by simp at ht; omega
        rw [g.nonanticipating t h h' (fun s h1 h2 => hh s (by omega)),
          hrule.2.2 t h h' (fun s h1 h2 => hh s (by omega)), hh t ht'])).add_const B
  have hcompl : ∀ k, P (E k)ᶜ ≤ ENNReal.ofReal (δ / K) := by
    intro k
    rw [prob_compl_eq_one_sub (hEmeas k)]
    have h1 := hEprob k
    rw [ENNReal.ofReal_sub _ hδK0.le, ENNReal.ofReal_one] at h1
    calc 1 - P (E k) ≤ 1 - (1 - ENNReal.ofReal (δ / K)) := tsub_le_tsub_left h1 _
      _ = ENNReal.ofReal (δ / K) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top]
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hδK1.le
  set Eall := ⋂ k, E k with hEall
  have hEallm : MeasurableSet Eall := MeasurableSet.iInter hEmeas
  have hEallc : P Eallᶜ ≤ ENNReal.ofReal δ := by
    rw [hEall, Set.compl_iInter]
    calc P (⋃ k, (E k)ᶜ) ≤ ∑ k, P (E k)ᶜ := measure_iUnion_fintype_le P _
      _ ≤ ∑ _k : Fin K, ENNReal.ofReal (δ / K) := Finset.sum_le_sum (fun k _ => hcompl k)
      _ = ENNReal.ofReal δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hEallp : ENNReal.ofReal (1 - δ) ≤ P Eall := by
    have := prob_compl_eq_one_sub hEallm (μ := P)
    rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one]
    have h2 : P Eall = 1 - P Eallᶜ := by
      rw [prob_compl_eq_one_sub hEallm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rw [h2]
    exact tsub_le_tsub_left hEallc _
  refine hEallp.trans (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq]
  have hgood : ∀ k, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) k ≤
      ∑ t ∈ Finset.Icc 1 n, est β γ η g t (fun s => I s ω) k + B := by
    intro k
    have := Set.mem_iInter.1 hω k
    exact this
  unfold regret
  have hle : ∀ k, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) k ≤
      β * n * K + γ * n + (1 + β) * η * K * n + B + Real.log K / η +
        ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω) := by
    intro k
    have := pathwise β γ η g hK0 hβ0.le hη hγ0 hγ hβηγ n (fun s => I s ω) B hB hgood k
    linarith
  have hne : Nonempty (Fin K) := ⟨⟨0, hK0⟩⟩
  have := ciSup_le hle
  linarith
