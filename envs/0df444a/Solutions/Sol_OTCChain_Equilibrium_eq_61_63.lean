-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_61_63
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:46:35.260156+00:00
-- url     : https://prove2.me/submissions/cfa1416d-7d88-486d-9176-645f3bebf70a

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb) (h1 : Δb < Δs)
    (h2 : Δs < M.Δbar) (μ : Densities) (hμ : IsSteadyState M Δb Δs μ) :
    ∀ Δ ∈ Ioc Δs M.Δbar, μ.μn Δ = 0 ∧ μ.μs Δ = 0 ∧
      μ.μb Δ = M.κ * (M.N - M.X) / (M.κ + M.lam * μ.Ns M) * M.f Δ ∧
      μ.μh Δ = (M.κ * M.X + M.lam * μ.Ns M * M.N) / (M.κ + M.lam * μ.Ns M) * M.f Δ := by
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, hc, hD, hf, hfi, hf1⟩ := hM
  obtain ⟨hnn, -, -, -, -, h12, h14, -, -, -⟩ := hμ
  intro Δ hΔ
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨by linarith [hΔ.1], hΔ.2⟩
  obtain ⟨e1, e2, e3⟩ := h14 Δ hΔ
  have e4 := h12 Δ hΔI
  have hNs : 0 ≤ μ.Ns M := by
    unfold Densities.Ns
    exact intervalIntegral.integral_nonneg hD.le (fun u hu => (hnn u hu).2.1)
  have hpos : 0 < M.κ + M.lam * μ.Ns M := by positivity
  rw [e1, e2] at e4
  have hb : μ.μb Δ = M.κ * (M.N - M.X) / (M.κ + M.lam * μ.Ns M) * M.f Δ := by
    rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
    nlinarith
  refine ⟨e1, e2, hb, ?_⟩
  have hh : μ.μh Δ = M.N * M.f Δ - μ.μb Δ := by linarith
  rw [hh, hb]
  field_simp
  ring
