-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_55_57
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:46:34.310081+00:00
-- url     : https://prove2.me/submissions/39395e36-0a41-4415-a070-d830fa7c405f

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    ∀ Δ ∈ Ico 0 Δb, μ.μb Δ = 0 ∧ μ.μh Δ = 0 ∧
      μ.μn Δ = (M.κ * (M.N - M.X) + M.lam * μ.Nb M * M.N) / (M.κ + M.lam * μ.Nb M) * M.f Δ ∧
      μ.μs Δ = M.κ * M.X / (M.κ + M.lam * μ.Nb M) * M.f Δ := by
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, hc, hD, hf, hfi, hf1⟩ := hM
  obtain ⟨hnn, -, -, -, -, h12, -, h16, -, -⟩ := hμ
  intro Δ hΔ
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨hΔ.1, by linarith [hΔ.2]⟩
  obtain ⟨e1, e2, e3⟩ := h16 Δ hΔ
  have e4 := h12 Δ hΔI
  have hNb : 0 ≤ μ.Nb M := by
    unfold Densities.Nb
    exact intervalIntegral.integral_nonneg hD.le (fun u hu => (hnn u hu).1)
  have hpos : 0 < M.κ + M.lam * μ.Nb M := by positivity
  rw [e1, e2] at e4
  have hs : μ.μs Δ = M.κ * M.X / (M.κ + M.lam * μ.Nb M) * M.f Δ := by
    rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
    nlinarith
  refine ⟨e1, e2, ?_, hs⟩
  have hn : μ.μn Δ = M.N * M.f Δ - μ.μs Δ := by linarith
  rw [hn, hs]
  field_simp
  ring
