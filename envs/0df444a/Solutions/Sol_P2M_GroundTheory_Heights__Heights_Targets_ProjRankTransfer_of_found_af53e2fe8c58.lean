-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_of_found_af53e2fe8c58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:30.042826+00:00
-- url     : https://prove2.me/submissions/ceea07ee-5c4d-4766-b3bd-47766a56b72c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDensVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankTransfer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRankTransfer
theorem _root_.solution (hEq : ProjPotMassEq.Statement) (hPos : ProjPotMassPos.Statement)
    (hVan : ProjPotDensVanish.Statement) : ProjRankTransfer.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  by_contra hno
  push Not at hno
  have := ProjRankTransfer.locallyConnectedSpace BV
  have hCo : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have h1 := hEq K ι P J n R Ψ V BV hH hC hΨ _ ⟨isClosed_connectedComponent, hCo⟩
  have h2 := hPos K ι P J n R V BV hH hC _ hCo ⟨x, mem_connectedComponent, hx⟩
  have h3 : mInt BV (fun _ => projPot R Ψ V)
      ((connectedComponent x).indicator fun _ => (1 : ℝ)) = 0 := by
    unfold mInt
    split_ifs with hP
    · unfold integralWith
      refine Finset.sum_eq_zero fun j _ => setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      by_cases hm : (BV.chart j).symm u ∈ connectedComponent x
      · rw [hVan K ι P J n R Ψ V BV hH hΨ j u hu (hno _ hm), mul_zero]
      · rw [Set.indicator_of_notMem hm, mul_zero, zero_mul]
    · rfl
  linarith
end ProjRankTransfer
end GroundTheory.Heights₂.Heights.Targets
