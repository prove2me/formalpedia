-- Prove2me | solution 1 for RefMNLPricing.Myopic.revenue_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:47:34.274929+00:00
-- url     : https://prove2.me/submissions/53bdf3f0-a51e-464c-b226-e3dd19b8f0a6

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Theorems.Thm_RefMNLPricing_Myopic_theorem_2

open RefMNLPricing.Myopic

namespace RefMNLRevMonoAux

lemma rev_mul {n : ℕ} (a b cp cm q r : Fin n → ℝ) :
    revenue a b cp cm q r * (1 + ∑ k, Real.exp (util a b cp cm q r k)) =
      ∑ k, q k * Real.exp (util a b cp cm q r k) := by
  have hD : 0 < 1 + ∑ k, Real.exp (util a b cp cm q r k) := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
      (Real.exp_pos (util a b cp cm q r k)).le)
    linarith
  unfold revenue share
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp

/-- Every coordinate of a box maximiser is at least the optimal revenue (Theorem 2). -/
lemma price_ge_rev {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r p : Fin n → ℝ) (hr : InBox pH r) (hp : IsBoxMax a b cp cm pH r p) (k : Fin n) :
    revenue a b cp cm p r ≤ p k := by
  obtain ⟨h1, h2, h3⟩ := theorem_2 a b cp cm pH hb hcp hcm hpH hceil r p hr hp k
  set v := revenue a b cp cm p r
  have hl : 0 < 1 / (b k + cm k) := by have := hb k; have := hcm k; positivity
  have hh : 0 < 1 / (b k + cp k) := by have := hb k; have := hcp k; positivity
  rcases lt_trichotomy (cp k) (cm k) with hc | hc | hc
  · obtain ⟨a1, a2, a3⟩ := h1 hc
    by_cases e1 : r k < v + 1 / (b k + cm k)
    · rw [a1 e1]; linarith
    · by_cases e2 : v + 1 / (b k + cp k) < r k
      · rw [a2 e2]; linarith
      · push_neg at e1 e2
        rw [a3 e1 e2]; linarith
  · rw [h2 hc]; linarith
  · obtain ⟨_, a1, a2, a3⟩ := h3 hc
    rcases lt_trichotomy (r k) (v + Zgap b cp cm k) with e | e | e
    · rw [a1 e]; linarith
    · rcases a3 e with f | f <;> rw [f] <;> linarith
    · rw [a2 e]; linarith

lemma util_mono {n : ℕ} (a b cp cm : Fin n → ℝ) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (p r r' : Fin n → ℝ) (hle : r ≤ r') (k : Fin n) :
    util a b cp cm p r k ≤ util a b cp cm p r' k := by
  unfold util
  have h1 : max (r k - p k) 0 ≤ max (r' k - p k) 0 := max_le_max (by linarith [hle k]) le_rfl
  have h2 : max (p k - r' k) 0 ≤ max (p k - r k) 0 := max_le_max (by linarith [hle k]) le_rfl
  have := mul_le_mul_of_nonneg_left h1 (hcp k)
  have := mul_le_mul_of_nonneg_left h2 (hcm k)
  linarith

end RefMNLRevMonoAux

open RefMNLRevMonoAux in
theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r r' p p' : Fin n → ℝ) (hr : InBox pH r) (hr' : InBox pH r') (hle : r ≤ r')
    (hp : IsBoxMax a b cp cm pH r p) (hp' : IsBoxMax a b cp cm pH r' p') :
    revenue a b cp cm p r ≤ revenue a b cp cm p' r' := by
  set v := revenue a b cp cm p r with hv
  have hpk := price_ge_rev a b cp cm pH hb hcp hcm hpH hceil r p hr hp
  -- the identity `∑ (p_k - v) e^{u_k(p,r)} = v`
  have hid : ∑ k, (p k - v) * Real.exp (util a b cp cm p r k) = v := by
    have := rev_mul a b cp cm p r
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← this, ← hv]; ring
  have hmono : ∑ k, (p k - v) * Real.exp (util a b cp cm p r k) ≤
      ∑ k, (p k - v) * Real.exp (util a b cp cm p r' k) :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (util_mono a b cp cm hcp hcm p r r' hle k)) (by linarith [hpk k]))
  have h2 := rev_mul a b cp cm p r'
  have hS : 0 ≤ ∑ k, Real.exp (util a b cp cm p r' k) :=
    Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  have h3 : ∑ k, (p k - v) * Real.exp (util a b cp cm p r' k) =
      ∑ k, p k * Real.exp (util a b cp cm p r' k) - v * ∑ k, Real.exp (util a b cp cm p r' k) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hge : v ≤ revenue a b cp cm p r' := by
    by_contra hlt
    push_neg at hlt
    have : revenue a b cp cm p r' * (1 + ∑ k, Real.exp (util a b cp cm p r' k)) <
        v * (1 + ∑ k, Real.exp (util a b cp cm p r' k)) :=
      mul_lt_mul_of_pos_right hlt (by linarith)
    nlinarith
  exact hge.trans (hp'.2 p hp.1)
