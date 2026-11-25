-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:36.305597+00:00
-- url     : https://prove2.me/submissions/4f965ece-e755-4a49-b7a1-a64c4d417c98

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.Targets.ProjPotDens.blockCLM_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution {κ α : Type*} [Fintype κ] (s : Finset α) (F : α → (κ → ℂ) → ℝ)
    {z : κ → ℂ} (hF : ∀ a ∈ s, ContDiffAt ℝ 2 (F a) z) (v : κ → ℂ) :
    levi (fun y => ∑ a ∈ s, F a y) z v = ∑ a ∈ s, levi (F a) z v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, F b y) z :=
      ContDiffAt.sum fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have h := levi_add_smul (f := F a) (g := fun y => ∑ b ∈ s, F b y) 1
      (hF a (Finset.mem_insert_self a s)) hs v
    simp only [one_mul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih fun b hb => hF b (Finset.mem_insert_of_mem hb)]
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
