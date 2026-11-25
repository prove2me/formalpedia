-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.opGelfand_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:27.049804+00:00
-- url     : https://prove2.me/submissions/d99499b4-eb97-4135-a74b-d36f852b002c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_opPow_eqOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Y a b)) k F z =
      c ^ k * ((gelfand (fun a b => eOp (X a b)) k G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  simp only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.mul_sum]
  exact Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z)
    (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) :
      Matrix (Fin n) (Fin n) ℂ → ℂ) z)
    fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz
end ReciprocityTheory.ChartRestriction.DS.S7
