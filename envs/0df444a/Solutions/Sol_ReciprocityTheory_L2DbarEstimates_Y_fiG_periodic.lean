-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiG_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:22.556885+00:00
-- url     : https://prove2.me/submissions/4b14073a-1110-4ddd-9cca-d916bc737ccb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hper : ∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) (ν : Fin f → ℤ) :
    ∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, fiG h ν (s + fun k => (m k : ℂ)) = fiG h ν s := by
  intro s hs m
  unfold fiG
  rw [hper s hs m]
  congr 1
  have hsum : ∑ k, (ν k : ℂ) * (s + fun k => (m k : ℂ)) k =
      ∑ k, (ν k : ℂ) * s k + ((∑ k, ν k * m k : ℤ) : ℂ) := by
    push_cast
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum, mul_add, Complex.exp_add]
  have h2 : Complex.exp (-2 * Real.pi * Complex.I * ((∑ k, ν k * m k : ℤ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (-(∑ k, ν k * m k))]
    congr 1
    push_cast
    ring
  rw [h2, mul_one]
end ReciprocityTheory.L2DbarEstimates.Y
