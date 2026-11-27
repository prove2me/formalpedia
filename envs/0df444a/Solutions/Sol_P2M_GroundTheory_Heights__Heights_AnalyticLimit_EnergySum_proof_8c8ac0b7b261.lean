-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_EnergySum_proof_8c8ac0b7b261
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:57.978801+00:00
-- url     : https://prove2.me/submissions/af03d3eb-c4ce-4967-93cd-b17b362c5920

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_tvInt_lincomb_le_5b348dfe4313

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
namespace EnergySum
theorem _root_.solution : EnergySum.Statement := by
  intro D X _ A Yo m P a V hpot hnn hσ
  refine (tvInt_lincomb_le A Yo P a hpot hnn fun σ => (hσ σ).1).trans ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_left (hσ σ).2 (Finset.prod_nonneg fun k _ => abs_nonneg _)
end EnergySum
end GroundTheory.Heights₂.Heights.AnalyticLimit
