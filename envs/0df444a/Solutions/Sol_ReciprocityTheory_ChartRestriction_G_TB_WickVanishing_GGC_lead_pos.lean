-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:03.27315+00:00
-- url     : https://prove2.me/submissions/e2e9a9e3-b67a-464c-9aa5-ed283ff30004

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (i : ℕ) (hi : i ≤ r) :
    0 < (∏ a ∈ Finset.range i, (if a < p0 then (1 : ℝ) else -1)) *
      ((Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi)).det.re := by
  have hpd := h.submatrix (Fin.castLE_injective hi)
  have hsub : (diagonal (sv p0) * Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      diagonal (fun j : Fin i => sv p0 (Fin.castLE hi j)) * (Gy p0 y).submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp [Matrix.diagonal_mul]
  rw [hsub] at hpd
  have hd := hpd.det_pos
  rw [Matrix.det_mul, Matrix.det_diagonal] at hd
  have hprod : ∏ j : Fin i, sv p0 (Fin.castLE hi j) =
      ((∏ a ∈ Finset.range i, (if a < p0 then (1 : ℝ) else -1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [sv, Fin.val_castLE]
    split_ifs <;> simp
  rw [hprod] at hd
  have h2 := (Complex.lt_def.1 hd).1
  rw [Complex.re_ofReal_mul, Complex.zero_re] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
