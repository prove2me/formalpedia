-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_hessC_finset_sum_8ccaf9ba300e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:20.733456+00:00
-- url     : https://prove2.me/submissions/cc6f331b-ea8c-4843-bc72-18040add651a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_EnergySum
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_add__c2c0858c9e7b
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_hessC_const_mul__03a5d330ff52
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)
noncomputable section
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → (Fin D → ℂ) → ℝ)
    (z : Fin D → ℂ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hessC (fun w => ∑ i ∈ s, c i * f i w) z = ∑ i ∈ s, (c i : ℂ) • hessC (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ReciprocityTheory.AnForm.M.hessC_const_mul' (D := D) 0 (fun _ => (0 : ℝ)) z
    simpa using h
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z (contDiffAt_const.mul (hf i (Finset.mem_insert_self _ _)))
      (ContDiffAt.sum fun i' hi' => contDiffAt_const.mul (hf i' (Finset.mem_insert_of_mem hi'))),
      ReciprocityTheory.AnForm.M.hessC_const_mul', ih fun i' hi' => hf i' (Finset.mem_insert_of_mem hi')]
end GroundTheory.Heights₂.Heights.AnalyticLimit
