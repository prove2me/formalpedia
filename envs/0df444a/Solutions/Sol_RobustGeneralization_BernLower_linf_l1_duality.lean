-- Prove2me | solution 1 for RobustGeneralization.BernLower.linf_l1_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:38:56.219669+00:00
-- url     : https://prove2.me/submissions/dbc8fbc5-96d9-4a21-81a1-107c0e3b8cbc

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

lemma aux_ld_inner (d : ℕ) (a b : E d) : inner ℝ a b = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

lemma aux_ld_smul (d : ℕ) (y : Bool) (w : E d) (i : Fin d) :
    (lab y • w) i = lab y * w i := by
  simp

lemma aux_ld_abs (d : ℕ) (y : Bool) (w : E d) (i : Fin d) : |(lab y • w) i| = |w i| := by
  rw [aux_ld_smul, abs_mul]
  cases y <;> simp [lab]

/-- Upper bound: `⟨v, Δ⟩ ≤ ε ∑ |v i|` whenever `|Δ i| ≤ ε`. -/
lemma aux_ld_upper (d : ℕ) (v Δ : E d) (ε : ℝ) (hΔ : ∀ i, |Δ i| ≤ ε) :
    inner ℝ v Δ ≤ ε * ∑ i, |v i| := by
  rw [aux_ld_inner, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc v i * Δ i ≤ |v i * Δ i| := le_abs_self _
    _ = |v i| * |Δ i| := abs_mul _ _
    _ ≤ |v i| * ε := mul_le_mul_of_nonneg_left (hΔ i) (abs_nonneg _)
    _ = ε * |v i| := mul_comm _ _

/-- The maximizing perturbation `Δ i = ε · sign (v i)`. -/
noncomputable def aux_ld_opt (d : ℕ) (v : E d) (ε : ℝ) : E d :=
  WithLp.toLp 2 (fun i => if 0 ≤ v i then ε else -ε)

lemma aux_ld_opt_bound (d : ℕ) (v : E d) (ε : ℝ) (hε : 0 ≤ ε) (i : Fin d) :
    |aux_ld_opt d v ε i| ≤ ε := by
  show |(if 0 ≤ v i then ε else -ε)| ≤ ε
  split_ifs <;> simp [abs_of_nonneg hε]

lemma aux_ld_opt_inner (d : ℕ) (v : E d) (ε : ℝ) :
    inner ℝ v (aux_ld_opt d v ε) = ε * ∑ i, |v i| := by
  rw [aux_ld_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  show v i * (if 0 ≤ v i then ε else -ε) = ε * |v i|
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

end RobustGeneralization.BernLower

open RobustGeneralization.BernLower

theorem solution (d : ℕ) (w x : E d) (y : Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {t : ℝ | ∃ Δ : E d, (∀ i, |Δ i| ≤ ε) ∧ t = inner ℝ (lab y • w) Δ}
        (ε * ∑ i, |w i|) ∧
      ((∀ x' ∈ linfBall x ε, 0 < inner ℝ (lab y • w) x') ↔
        ε * ∑ i, |w i| < inner ℝ (lab y • w) x) := by
  have hsum : ∑ i, |(lab y • w) i| = ∑ i, |w i| :=
    Finset.sum_congr rfl (fun i _ => aux_ld_abs d y w i)
  set v : E d := lab y • w with hv
  refine ⟨⟨⟨aux_ld_opt d v ε, aux_ld_opt_bound d v ε hε, ?_⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [aux_ld_opt_inner, hsum]
  · rintro t ⟨Δ, hΔ, rfl⟩
    rw [← hsum]
    exact aux_ld_upper d v Δ ε hΔ
  · intro h
    have hmem : x - aux_ld_opt d v ε ∈ linfBall x ε := by
      intro i
      have := aux_ld_opt_bound d v ε hε i
      simpa [abs_neg] using this
    have := h _ hmem
    rw [inner_sub_right, aux_ld_opt_inner, hsum] at this
    linarith
  · intro h x' hx'
    have hb : ∀ i, |(x - x') i| ≤ ε := by
      intro i
      have := hx' i
      rw [abs_sub_comm] at this
      simpa using this
    have hup := aux_ld_upper d v (x - x') ε hb
    rw [inner_sub_right, hsum] at hup
    linarith
