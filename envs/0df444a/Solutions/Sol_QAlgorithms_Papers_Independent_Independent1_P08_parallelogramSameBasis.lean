-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.parallelogramSameBasis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:04:32.875551+00:00
-- url     : https://prove2.me/submissions/55418472-f83b-4742-97f9-4b2313e6c4f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_planarSameBasis

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

theorem solution (t : Bloch) (l3 : ℝ) :
    convexHull ℝ (planarSliceMaps t l3) ⊆ convexHull ℝ canonicalCQ := by
  apply convexHull_min ?_ (convex_convexHull ℝ canonicalCQ)
  intro Φ hΦ
  obtain ⟨lam, hEq, hEBT, _h3, hzero⟩ := hΦ
  subst Φ
  rcases hzero with h0 | h1
  · have hplanar := (planarSameBasis).1 t lam hEBT 0 h0
    have hsubset : planarCQ 0 ⊆ canonicalCQ := by
      intro Ψ hΨ
      obtain ⟨t', lam', hΨeq, hCQ, _hz, _hcard⟩ := hΨ
      exact ⟨t', lam', hΨeq, hCQ⟩
    exact convexHull_mono hsubset hplanar
  · have hplanar := (planarSameBasis).1 t lam hEBT 1 h1
    have hsubset : planarCQ 1 ⊆ canonicalCQ := by
      intro Ψ hΨ
      obtain ⟨t', lam', hΨeq, hCQ, _hz, _hcard⟩ := hΨ
      exact ⟨t', lam', hΨeq, hCQ⟩
    exact convexHull_mono hsubset hplanar
