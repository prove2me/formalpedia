-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:20.705046+00:00
-- url     : https://prove2.me/submissions/fdec8627-45f6-4130-816a-842f82d0f195

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {K : Type*} [Field K] {t r : ℕ} (M : Matrix (Fin t) (Fin r) K)
    (hM : ∀ c : Fin r → K, M.mulVec c = 0 → c = 0) :
    ∃ a : Fin r → Fin t, (M.submatrix a id).det ≠ 0 := by
  classical

  have hspan : Submodule.span K (Set.range fun i => M i) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hfx : ∀ x : Fin r → K, f x = ∑ k, x k * f (Pi.single k 1) := by
      intro x
      conv_lhs => rw [← (Pi.basisFun K (Fin r)).sum_repr x]
      simp [map_sum, smul_eq_mul]
    have hc : M.mulVec (fun k => f (Pi.single k 1)) = 0 := by
      funext i
      have hi : M i ∈ LinearMap.ker f := hf (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, hfx] at hi
      exact hi
    have hc0 := hM _ hc
    apply hf0
    apply (Pi.basisFun K (Fin r)).ext
    intro k
    have hk := congrFun hc0 k
    simpa using hk

  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun i => M i)
  have hsp' : Submodule.span K (Set.range ((fun i => M i) ∘ a)) = ⊤ := hsp.trans hspan
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let B := Module.Basis.mk hli hsp'.ge
  have hcard : Fintype.card κ = r := by
    have h := Module.finrank_eq_card_basis B
    simpa using h.symm
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli2 : LinearIndependent K (Matrix.row (M.submatrix (a ∘ e) id)) :=
    hli.comp e e.injective
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hli2
  exact hli2
end ReciprocityTheory.AnForm.R
