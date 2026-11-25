-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_one_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:23.140276+00:00
-- url     : https://prove2.me/submissions/2f187907-c026-45c2-9797-90983a15ed19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped BigOperators ComplexOrder
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by
  have hHerm := hH.isHermitian
  have htr : ∑ i, hHerm.eigenvalues i = N := by
    have h := hHerm.trace_eq_sum_eigenvalues
    have h2 : H.trace = N := by simp [Matrix.trace, hd]
    rw [h2] at h
    have h4 := congrArg (RCLike.re : ℂ → ℝ) h
    simp only [map_sum, RCLike.ofReal_re, RCLike.natCast_re] at h4
    linarith
  have hre : H.det.re = ∏ i, hHerm.eigenvalues i := by
    rw [hHerm.det_eq_prod_eigenvalues]
    first
      | (norm_cast)
      | simp [← Complex.ofReal_prod]
  rw [hre]
  calc ∏ i, hHerm.eigenvalues i ≤ ∏ i, Real.exp (hHerm.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hH.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hHerm.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hHerm.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by simp [Finset.sum_sub_distrib, htr]
end ReciprocityTheory.ChartRestriction.G.T0
