-- Prove2me | solution 1 for WeightedRootIntegralIdentity.slit_keyhole_region_isOpen_v3
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T11:19:12.856839+00:00
-- url     : https://prove2.me/submissions/35381e9e-9671-4fb3-8aa6-f8539049fc6f

import Definitions.Def_slitKeyholeRegion

theorem solution {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    IsOpen (slitKeyholeRegion r R) := by
  rw [slitKeyholeRegion]
  have hopen1 : IsOpen {z : ℂ | r < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hopen2 : IsOpen {z : ℂ | ‖z‖ < R} := isOpen_lt continuous_norm continuous_const
  have hclosed_slit : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
    exact (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hopen3 : IsOpen {z : ℂ | ¬ (z.im = 0 ∧ 0 ≤ z.re)} := hclosed_slit.isOpen_compl
  convert (hopen1.inter hopen2).inter hopen3 using 1
  ext z
  simp [slitKeyholeRegion, and_assoc]
