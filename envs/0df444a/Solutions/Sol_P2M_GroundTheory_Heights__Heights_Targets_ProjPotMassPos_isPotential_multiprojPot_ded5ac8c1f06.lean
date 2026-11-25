-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_multiprojPot_ded5ac8c1f06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:23.722198+00:00
-- url     : https://prove2.me/submissions/beb0006e-a18b-4b45-a759-52169e823010

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_isSmoothHerm_fsLine_09ffc6e56251
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialPullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPotential_potOf
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjPotMassPos
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val) :
    IsPotential BV (multiprojPot R V) := by
  let L : HermLine ι := CurveDegreeVert.fsLine (fun _ : K => 2)
  have hL : L.h = fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ ((2 : ℕ) : ℤ) := by
    funext z
    simp only [L, CurveDegreeVert.fsLine, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]
  have h1 := isPotentialPullback R.A BV Subtype.val hH (potOf R L)
    (isPotential_potOf R (CurveDegreeVert.isSmoothHerm_fsLine _))
  refine ProjPotMassPos.isPotential_congr (P := (potOf R L).pullback Subtype.val hH.1) (fun _ => rfl) (fun y z hz => ?_) h1
  have hm := (R.mem y.1 z.1 hz).1
  show Real.log (L.h (R.lift y.1 z.1)) = ∑ k, Real.log (∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
  have hpos : ∀ k, 0 < ∑ i, ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hm k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun i => ‖R.lift y.1 z.1 ⟨k, i⟩‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i))
  rw [hL]
  simp only [zpow_natCast, Real.sq_sqrt (hpos _).le]
  exact Real.log_prod (fun k _ => (hpos k).ne')
end ProjPotMassPos
end GroundTheory.Heights₂.Heights.Targets
