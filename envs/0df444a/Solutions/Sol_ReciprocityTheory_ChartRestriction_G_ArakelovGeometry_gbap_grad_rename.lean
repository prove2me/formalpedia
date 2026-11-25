-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_grad_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:36.830198+00:00
-- url     : https://prove2.me/submissions/45aaa3df-79e4-4ca6-ba4a-e90edbfb72d7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] {n : ℕ} (e : J ≃ Fin n) (z₀ : J → ℂ)
    (f : MvPolynomial J ℤ) (j : Fin n) :
    grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e f)) j =
      eval z₀ (pderiv (e.symm j) (map (Int.castRingHom ℂ) f)) := by
  unfold grad
  have h := pderiv_rename (R := ℂ) e.injective (e.symm j) (map (Int.castRingHom ℂ) f)
  rw [Equiv.apply_symm_apply] at h
  have hc : (fun j => z₀ (e.symm j)) ∘ e = z₀ := by
    funext i
    simp
  rw [map_rename, h, eval_rename, hc]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
