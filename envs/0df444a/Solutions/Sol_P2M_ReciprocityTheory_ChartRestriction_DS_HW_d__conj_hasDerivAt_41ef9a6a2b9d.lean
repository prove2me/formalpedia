-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:23.753123+00:00
-- url     : https://prove2.me/submissions/efd2c8de-3ef5-4fd2-82fb-08777ac14228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_mat_conj_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => T.dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (T.dτ (X * Y - Y * X)) 0 := by
  have h := ((LinearMap.toContinuousLinearMap T.dτ).hasFDerivAt).comp_hasDerivAt _
    (mat_conj_hasDerivAt X Y)
  exact hasDerivAt_real_of_complex' (z := 0) h
end ReciprocityTheory.ChartRestriction.DS.HW
