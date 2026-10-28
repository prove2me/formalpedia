-- Prove2me | solution 1 for PrivAcq.Central.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:29:56.95204+00:00
-- url     : https://prove2.me/submissions/20cda5c3-1e92-48ab-86ae-f7e417e7880e

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivAcq_Central_CentralDP

open MeasureTheory

open PrivAcq.Central in
theorem AuxPrivAcq_lemma2_lemma1 {X : Type*} {n : ℕ} (f : (Fin n → X) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (L : Fin n → ℝ)
    (hL : ∀ i : Fin n, ∀ x x' : Fin n → X, (∀ j : Fin n, j ≠ i → x j = x' j) →
      |f x - f x'| ≤ L i) :
    IsCentralDP (fun x => (PrivLearn.Generic.laplace (1 / ε)).map (fun u => f x + u))
      (fun i => ε * L i) := by
  intro i S S' hSS' W hW
  set g : ℝ → ℝ → ENNReal := fun c v =>
    ENNReal.ofReal (Real.exp (-|v - c| / (1 / ε)) / (2 * (1 / ε))) with hg
  have hmap : ∀ c : ℝ, (PrivLearn.Generic.laplace (1 / ε)).map (fun u => c + u) W =
      ∫⁻ v, W.indicator (g c) v := by
    intro c
    rw [Measure.map_apply (measurable_const_add c) hW]
    unfold PrivLearn.Generic.laplace
    rw [withDensity_apply _ (measurable_const_add c hW)]
    rw [← lintegral_indicator (measurable_const_add c hW)]
    have : ∀ u, ((fun u => c + u) ⁻¹' W).indicator
        (fun x => ENNReal.ofReal (Real.exp (-|x| / (1 / ε)) / (2 * (1 / ε)))) u =
        W.indicator (g c) (c + u) := by
      intro u
      by_cases h : c + u ∈ W <;> simp [Set.indicator, h, hg]
    simp_rw [this]
    exact lintegral_add_left_eq_self (fun v => W.indicator (g c) v) c
  show (PrivLearn.Generic.laplace (1 / ε)).map (fun u => f S + u) W ≤
    ENNReal.ofReal (Real.exp (ε * L i)) * (PrivLearn.Generic.laplace (1 / ε)).map (fun u => f S' + u) W
  rw [hmap, hmap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  have hd := hL i S S' hSS'
  by_cases hv : v ∈ W
  · simp only [Set.indicator_of_mem hv, hg]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have htri : |v - f S'| ≤ |v - f S| + |f S - f S'| := by
      have := abs_sub_le v (f S) (f S')
      linarith
    have e1 : -|v - f S| / (1 / ε) = -(ε * |v - f S|) := by field_simp
    have e2 : -|v - f S'| / (1 / ε) = -(ε * |v - f S'|) := by field_simp
    rw [e1, e2]
    have hexp : Real.exp (-(ε * |v - f S|)) ≤ Real.exp (ε * L i) * Real.exp (-(ε * |v - f S'|)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hpos : 0 < 2 * (1 / ε) := by positivity
    have := div_le_div_of_nonneg_right hexp hpos.le
    rw [mul_div_assoc] at this
    exact this
  · simp [Set.indicator_of_notMem hv]

open PrivAcq.Central in
theorem solution {n : ℕ} (θ η : ℝ) (hη : 0 < η) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    IsCentralDP (X := Set.Icc (θ - 1 / 2) (θ + 1 / 2))
      (fun x => (PrivLearn.Generic.laplace (1 / η)).map (fun u => ∑ i, w i * (x i : ℝ) + u))
      (fun i => w i * η) := by
  have h := AuxPrivAcq_lemma2_lemma1 (X := Set.Icc (θ - 1 / 2) (θ + 1 / 2))
    (fun x => ∑ i, w i * (x i : ℝ)) η hη w (by
      intro i x x' hxx'
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · rw [← mul_sub, abs_mul, abs_of_nonneg (hw i)]
        have h1 := (x i).2
        have h2 := (x' i).2
        have : |(x i : ℝ) - (x' i : ℝ)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        nlinarith [hw i]
      · intro j _ hj
        rw [hxx' j hj, sub_self]
      · intro hi; exact absurd (Finset.mem_univ i) hi)
  intro i S S' hSS' W hW
  have := h i S S' hSS' W hW
  simp only at this ⊢
  rw [mul_comm (w i) η]
  exact this
