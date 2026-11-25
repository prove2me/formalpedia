-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_surj_of_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:48.060937+00:00
-- url     : https://prove2.me/submissions/2a940f43-fa42-47fd-b036-3a0f793da371

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
theorem _root_.solution {n c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ)
    (hli : LinearIndependent ℂ (fun i => grad p (F i))) :
    Function.Surjective (fun v : Fin n → ℂ => fun i => ∑ j, eval p (pderiv j (F i)) * v j) := by
  let M : Matrix (Fin c) (Fin n) ℂ := Matrix.of fun i j => eval p (pderiv j (F i))
  have hli' : LinearIndependent ℂ M.row := hli
  have hrank : M.rank = c := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli', Fintype.card_fin]
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  intro y
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop y
  exact ⟨v, by rw [← hv]; rfl⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
