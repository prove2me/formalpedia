-- Prove2me | solution 1 for RobustSpecClust.Est.eq_E18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:07:53.158984+00:00
-- url     : https://prove2.me/submissions/5efb7145-f753-48b3-a5eb-9926b3822b4d

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

open RobustSpecClust.Est in
theorem solution {d r : ℕ} (hr : 2 ≤ r) (μ : Fin r → E d) (κ : ℝ) (hκ : 0 < κ)
    (hΔ : 0 < Δmin μ hr) :
    let θ := κ * Δmin μ hr
    let τin := Real.exp (-(5 * Δmin μ hr ^ 2) / (64 * θ ^ 2))
    let τout : Fin r → Fin r → ℝ := fun k l => Real.exp (-(sep μ k l ^ 2) / (4 * θ ^ 2))
    tauOutMax τout hr = Real.exp (-(Δmin μ hr ^ 2) / (4 * θ ^ 2)) ∧
    τin - tauOutMax τout hr = Real.exp (-(5 / (64 * κ ^ 2))) - Real.exp (-(1 / (4 * κ ^ 2))) ∧
    0 < Real.exp (-(5 / (64 * κ ^ 2))) - Real.exp (-(1 / (4 * κ ^ 2))) := by
  intro θ τin τout
  have hc : 0 < 4 * θ ^ 2 := by
    have : 0 < θ := mul_pos hκ hΔ
    positivity
  have h1 : tauOutMax τout hr = Real.exp (-(Δmin μ hr ^ 2) / (4 * θ ^ 2)) := by
    apply le_antisymm
    · unfold tauOutMax
      apply Finset.sup'_le
      intro p hp
      have hle0 := Finset.inf'_le (s := (Finset.univ : Finset (Fin r)).offDiag)
        (fun p => sep μ p.1 p.2) hp
      have hle : Δmin μ hr ≤ sep μ p.1 p.2 := hle0
      show Real.exp (-(sep μ p.1 p.2 ^ 2) / (4 * θ ^ 2)) ≤ _
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hc.le
      exact neg_le_neg (pow_le_pow_left₀ hΔ.le hle 2)
    · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf' (offDiag_nonempty_of_two_le hr)
        (fun p => sep μ p.1 p.2)
      have hD : Δmin μ hr = sep μ p.1 p.2 := hpe
      have hle0 := Finset.le_sup' (s := (Finset.univ : Finset (Fin r)).offDiag)
        (fun p => τout p.1 p.2) hp
      have hle : τout p.1 p.2 ≤ tauOutMax τout hr := hle0
      have he : τout p.1 p.2 = Real.exp (-(Δmin μ hr ^ 2) / (4 * θ ^ 2)) := by
        show Real.exp (-(sep μ p.1 p.2 ^ 2) / (4 * θ ^ 2)) = _
        rw [← hD]
      rw [← he]
      exact hle
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    have hθ : θ = κ * Δmin μ hr := rfl
    have e1 : -(5 * Δmin μ hr ^ 2) / (64 * θ ^ 2) = -(5 / (64 * κ ^ 2)) := by
      rw [neg_div, neg_inj, div_eq_div_iff (by positivity) (by positivity), hθ]
      ring
    have e2 : -(Δmin μ hr ^ 2) / (4 * θ ^ 2) = -(1 / (4 * κ ^ 2)) := by
      rw [neg_div, neg_inj, div_eq_div_iff (by positivity) (by positivity), hθ]
      ring
    show Real.exp (-(5 * Δmin μ hr ^ 2) / (64 * θ ^ 2)) - _ = _
    rw [e1, e2]
  · rw [sub_pos, Real.exp_lt_exp, neg_lt_neg_iff, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_pos_of_pos hκ]
