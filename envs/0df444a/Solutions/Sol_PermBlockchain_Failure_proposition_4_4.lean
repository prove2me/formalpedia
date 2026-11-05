-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:41:36.870505+00:00
-- url     : https://prove2.me/submissions/f1a7b908-a79e-42d8-ab10-bb7091e85d09

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

namespace GTAux
open PermBlockchain.Failure Set

theorem tangent {f f' : ℝ → ℝ} (hc : ConvexOn ℝ (Ici (0:ℝ)) f)
    (hd : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt f (f' x) (Ici 0) x) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x + f' x * (y - x) ≤ f y := by
  have hx' : x ∈ Ici (0:ℝ) := hx
  have hy' : y ∈ Ici (0:ℝ) := hy
  rcases lt_trichotomy x y with h | h | h
  · have := hc.le_slope_of_hasDerivWithinAt hx' hy' h (hd x hx)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivWithinAt hy' hx' h (hd x hx)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

variable {m : ℕ} {M : Model m}

theorem exists_c (hM : M.Standing) {Δ : ℝ} (hA : M.Assumption1 Δ) :
    ∃ c : ℝ, 0 < c ∧ M.cl' c = M.γ := by
  set b := M.G ((M.L + Δ + M.L + M.h + M.l) / 2 - M.γ) with hb
  have hb0 : 0 ≤ b := ProbabilityTheory.cdf_nonneg _ _
  have hdar := exists_hasDerivWithinAt_eq_of_ge_of_le (f := M.cl) (f' := M.cl') hb0
    (fun x hx => (hM.hasDerivWithinAt_cl x hx.1).mono (fun y hy => hy.1)) hA.1.le hA.2.le
  obtain ⟨c, hc, hcg⟩ := hdar
  refine ⟨c, ?_, hcg⟩
  rcases hc.1.eq_or_lt with h | h
  · subst h; exact absurd hcg (ne_of_lt hA.1)
  · exact h

theorem cinv_nonneg (M : Model m) (x : ℝ) : 0 ≤ M.cinv x :=
  Real.sSup_nonneg (fun _ hs => hs.1)

theorem cinv_le (hM : M.Standing) {c x : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ)
    (hx : x ≤ M.γ) : M.cinv x ≤ c := by
  refine Real.sSup_le (fun t ht => ?_) hc
  by_contra hlt
  rw [not_le] at hlt
  have := hM.cl'_strictMonoOn hc ht.1 hlt
  linarith [ht.2]

theorem cinv_eq (hM : M.Standing) {c : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ) :
    M.cinv M.γ = c := by
  refine le_antisymm (cinv_le hM hc hcg le_rfl) ?_
  refine le_csSup ⟨c, fun t ht => ?_⟩ ⟨hc, hcg.le⟩
  by_contra hlt
  rw [not_le] at hlt
  have := hM.cl'_strictMonoOn hc ht.1 hlt
  linarith [ht.2]

theorem profit_le (hM : M.Standing) {c : ℝ} (hc : 0 ≤ c) (hcg : M.cl' c = M.γ) {s : ℝ}
    (hs : 0 ≤ s) : M.γ * s - M.cl s ≤ M.γ * c - M.cl c := by
  have := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl hc hs
  rw [hcg] at this
  linarith

theorem profit_pos (hM : M.Standing) {c : ℝ} (hc : 0 < c) (hcg : M.cl' c = M.γ) :
    0 < M.γ * c - M.cl c := by
  have h1 := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl (x := c / 2) (y := 0)
    (by linarith) le_rfl
  have h2 := tangent hM.cl_convexOn hM.hasDerivWithinAt_cl (x := c) (y := c / 2)
    hc.le (by linarith)
  have h3 : M.cl' (c / 2) < M.γ := by
    rw [← hcg]; exact hM.cl'_strictMonoOn (show (0:ℝ) ≤ c / 2 by linarith) hc.le (by linarith)
  rw [hM.cl_zero] at h1
  rw [hcg] at h2
  nlinarith

theorem WV_eq (X : Scenario) (Δ : ℝ) :
    M.WV X Δ = M.Ψl X Δ * M.sl X Δ - M.cl (M.sl X Δ) := by
  unfold Model.WV Model.Ψh; ring

end GTAux

open PermBlockchain.Failure in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) (Δ : ℝ) (hΔ : 0 < Δ)
    (hA : M.Assumption1 Δ) :
    M.WV .F Δ < M.WV .N Δ ∧ M.WV .P Δ < M.WV .N Δ := by
  obtain ⟨c, hc, hcg⟩ := GTAux.exists_c hM hA
  have hN : M.WV .N Δ = M.γ * c - M.cl c := by
    rw [GTAux.WV_eq]; simp only [Model.Ψl, Model.sl, GTAux.cinv_eq hM hc.le hcg]
  have key : ∀ p s : ℝ, p < M.γ → 0 ≤ s → p * s - M.cl s < M.γ * c - M.cl c := by
    intro p s hp hs
    rcases hs.eq_or_lt with h | h
    · subst h
      simp only [mul_zero, hM.cl_zero, sub_zero]
      exact GTAux.profit_pos hM hc hcg
    · have := GTAux.profit_le hM hc.le hcg hs
      nlinarith
  have hγ := hM.γ_pos
  have hhl := hM.l_lt_h
  constructor
  · rw [GTAux.WV_eq, hN]
    apply key
    · simp only [Model.Ψl]; apply max_lt <;> linarith
    · exact GTAux.cinv_nonneg M _
  · rw [GTAux.WV_eq, hN]
    apply key
    · simp only [Model.Ψl]; apply max_lt <;> linarith
    · exact GTAux.cinv_nonneg M _
