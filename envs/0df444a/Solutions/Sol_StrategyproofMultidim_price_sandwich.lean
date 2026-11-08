-- Prove2me | solution 1 for StrategyproofMultidim.price_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:28:43.940067+00:00
-- url     : https://prove2.me/submissions/6a24a856-37ae-40d8-869e-1ce9644b89fa

import Mathlib
import Definitions.Def_StrategyproofMultidim_SP

open StrategyproofMultidim in
theorem solution {n m : ℕ} (μ : Mechanism n m) (hSP : SP μ)
    (v : Fin n → Fin m → ℝ) (hv : PosProfile v) (i : Fin n) (x : Fin m → ℝ)
    (hx : ∀ k, 0 < x k) :
    bundleValue (μ.q (Function.update v i x) i) (v i) - bundleValue (μ.q v i) (v i) ≤
        μ.t i (Function.update v i x) - μ.t i v ∧
      μ.t i (Function.update v i x) - μ.t i v ≤
        bundleValue (μ.q (Function.update v i x) i) x - bundleValue (μ.q v i) x ∧
      (μ.q (Function.update v i x) i = μ.q v i →
        μ.t i (Function.update v i x) = μ.t i v) := by
  have hw : PosProfile (Function.update v i x) := by
    intro j k
    by_cases hj : j = i
    · subst hj; simp [hx k]
    · rw [Function.update_of_ne hj]; exact hv j k
  have h1 := hSP v hv i x hx
  have h2 := hSP (Function.update v i x) hw i (v i) (hv i)
  rw [Function.update_idem, Function.update_eq_self, Function.update_self] at h2
  unfold util at h1 h2
  refine ⟨by linarith, by linarith, ?_⟩
  intro hq
  rw [hq] at h1 h2
  linarith
