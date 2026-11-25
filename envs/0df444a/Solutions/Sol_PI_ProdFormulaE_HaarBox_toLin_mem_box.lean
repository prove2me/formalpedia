-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.toLin_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:47.975111+00:00
-- url     : https://prove2.me/submissions/96e09fb3-b53f-4a4a-97bd-0487efcc1db8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
import Theorems.Thm_PI_ProdFormulaE_HaarBox_repr_toLin
import Theorems.Thm_PI_ProdFormulaE_HaarBox_transvection_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel Module Matrix
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem tGamma_apply_of_ne (t : Matrix.TransvectionStruct ι K) {k : ι}
    (hk : k ≠ t.i) : tγ t k = 1 := by
  simp [tγ, hk]
private theorem tGamma_apply_self (t : Matrix.TransvectionStruct ι K) :
    tγ t t.i = max (valuation K t.c) 1 := by
  simp [tγ]
end PI.ProdFormulaE.HaarBox
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) (x : E)
    (hx : x ∈ box b (tγ t)) : Matrix.toLin b b t.toMatrix x ∈ box b (tγ t) := by
  change ∀ k, valuation K (b.repr x k) ≤ tγ t k at hx
  change ∀ k, valuation K (b.repr (Matrix.toLin b b t.toMatrix x) k) ≤ tγ t k
  intro k
  have e : b.repr (Matrix.toLin b b t.toMatrix x) k
      = b.repr x k + if k = t.i then t.c * b.repr x t.j else 0 := by
    rw [congrFun (repr_toLin b t.toMatrix x) k, transvection_mulVec]
  rw [e]
  by_cases hk : k = t.i
  · rw [if_pos hk]
    have hj : valuation K (b.repr x t.j) ≤ 1 := by
      have h := hx t.j
      rwa [tGamma_apply_of_ne t t.hij.symm] at h
    have hR : tγ t k = max (valuation K t.c) 1 := by
      rw [hk]; exact tGamma_apply_self t
    have hxi : valuation K (b.repr x k) ≤ max (valuation K t.c) 1 := by
      rw [← hR]; exact hx k
    rw [hR]
    refine (Valuation.map_add _ _ _).trans (max_le hxi ?_)
    rw [Valuation.map_mul]
    calc valuation K t.c * valuation K (b.repr x t.j) ≤ valuation K t.c * 1 := by
          first
          | exact mul_le_mul_left' hj _
          | gcongr
      _ = valuation K t.c := mul_one _
      _ ≤ max (valuation K t.c) 1 := le_max_left _ _
  · rw [if_neg hk, add_zero]
    exact hx k
end PI.ProdFormulaE.HaarBox
