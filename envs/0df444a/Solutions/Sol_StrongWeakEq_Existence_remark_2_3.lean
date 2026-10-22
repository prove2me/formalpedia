-- Prove2me | solution 1 for StrongWeakEq.Existence.remark_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:13:55.707882+00:00
-- url     : https://prove2.me/submissions/dd766994-e7b1-4290-90cc-752c21d91c42

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model

set_option autoImplicit false
open MeasureTheory Filter Topology StrongWeakEq.Existence

theorem solution {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (Qs : Matrix (Fin N) (Fin N) ℝ)
    (hQs : IsStrongEquilibrium D f Qs) :
    IsWeakEquilibrium D f Qs := by
  obtain ⟨hmem, hstrong⟩ := hQs
  refine ⟨hmem, fun Q hQ i η hη => ?_⟩
  obtain ⟨ε, hε, hle⟩ := hstrong Q hQ i
  have hev : ∀ᶠ ε' in 𝓝[>] (0:ℝ), ε' ∈ Set.Ioo (0:ℝ) ε :=
    Ioo_mem_nhdsGT hε
  filter_upwards [hev] with ε' hε'
  have h1 := hle ε' ⟨hε'.1, hε'.2.le⟩
  have h2 : 0 ≤ (payoff f Qs i - concatPayoff f ε' Q Qs i) / ε' :=
    div_nonneg (by linarith) hε'.1.le
  linarith
