-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.gelfand_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:10.46005+00:00
-- url     : https://prove2.me/submissions/d06306eb-d9a7-41e4-a40d-0e32abaa0b4b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiT_eqOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_xRev_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_xTr_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hw_rev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hw_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_rho_rev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isGlRep_eOp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_opGelfand_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfand_hw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem gval_comp_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    gval (fun r => l (σ r)) k = gval l k := by
  have h : (∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l (σ r)) * PowerSeries.X)⁻¹)) =
      ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹) :=
    Equiv.prod_comp σ (fun r => 1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)
  unfold gval gelfandSeries
  beta_reduce
  rw [h]
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (PhiM μ) z =
        ((-1 : ℂ) ^ k * gval (icShift lam) k) * PhiM μ z ∧
      opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (PhiM μ) z =
        gval (icShift (-lam)) k * PhiM μ z := by
  constructor
  · have hY : ∀ a b, Matrix.single a b (1 : ℂ) = (-1 : ℂ) • xRev n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xRev]
    have hν : ((fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) + rho n) = fun a => lam (Fin.revPerm a) := by
      funext a
      simp only [Pi.add_apply, Fin.revPerm_apply, hμ (Fin.rev a)]
      have := rho_rev_add (n := n) a
      linarith
    refine (opGelfand_eq (xRev n) _ Fin.revPerm (-1) hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xRev n) xRev_rel) (hw_rev μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz]
    rw [show icShift (fun a => lam (Fin.revPerm a)) = fun a => icShift lam (Fin.revPerm a) from rfl,
      gval_comp_perm]
    ring
  · have hY : ∀ a b, Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) =
        (1 : ℂ) • xTr n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xTr]
    have hν : ((fun a => -((μ a : ℤ) : ℝ)) + rho n) = -lam := by
      funext a
      simp only [Pi.add_apply, Pi.neg_apply, hμ a]
      ring
    refine (opGelfand_eq (xTr n) _ Fin.revPerm 1 hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xTr n) xTr_rel) (hw_tr μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz, one_pow, one_mul]
end ReciprocityTheory.ChartRestriction.DS.S7
