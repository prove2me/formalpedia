-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.prho_entry_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:32.134064+00:00
-- url     : https://prove2.me/submissions/5901bb72-bcc1-4e61-948c-49ce464e33db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h := (L.hasFDerivAt).comp_hasDerivAt _ (hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ))
  have h2 := hasDerivAt_real_of_complex' (z := 0) h
  have e : L (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by simp [L]
  exact h2.congr_deriv e
end ReciprocityTheory.ChartRestriction.DS.HW
