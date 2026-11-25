-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inner_crossOp_eig_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:22.708336+00:00
-- url     : https://prove2.me/submissions/f8b6ccfc-15fa-4661-9d0f-11d5128c252c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by
  have h := crossOp_symm hU 1 0 u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne : (θ : ℂ) ≠ (θ' : ℂ) := by exact_mod_cast hθ
  by_contra h0
  exact hne (mul_right_cancel₀ h0 h)
end ReciprocityTheory.ChartRestriction.DS
