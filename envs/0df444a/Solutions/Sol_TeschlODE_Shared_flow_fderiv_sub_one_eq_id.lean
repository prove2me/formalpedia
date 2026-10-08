-- Prove2me | solution 1 for TeschlODE.Shared.flow_fderiv_sub_one_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:17:47.858447+00:00
-- url     : https://prove2.me/submissions/404f6db4-8f4b-425e-bd18-b42f803e9096

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

open TeschlODE.Shared in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x : Fin n → ℝ) (s t : ℝ) (hx : x ∈ M) (hs : s ∈ I x) (ht : t ∈ I x) :
    fderiv ℝ (Φ (s - s)) x = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  rw [sub_self]
  have h : Φ 0 =ᶠ[nhds x] id := by
    filter_upwards [hM.mem_nhds hx] with y hy
    exact (hΦ y hy).2.2.1
  rw [h.fderiv_eq, fderiv_id]
