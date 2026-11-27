-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_proof_ece63d2cdc46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:24.65967+00:00
-- url     : https://prove2.me/submissions/b8e89856-5f36-4ebc-a988-fe183345aaac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDens
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_nonneg_of_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_pos_of_posDef
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posDef
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp


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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjPotDens
theorem _root_.solution : ProjPotDens.Statement := by
  intro K _ ι _ P J n R V BV hB j y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x, x ∈ (BV.chart j).source ∧ BV.chart j x = y :=
    ⟨_, (BV.chart j).map_target hy, (BV.chart j).right_inv hy⟩
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx

  have hdens : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      locDens BV (fun _ => multiprojPot R V) j (BV.chart j x) =
        ReciprocityTheory.AnForm.maDens (fun _ => ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
    intro p hp
    unfold locDens
    rw [hsx]
    exact maDens_congr_hessC _ _ _ fun _ => ProjPotDens.hessC_chartPot hB x hx p hp
  have hlevi : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      ContDiffAt ℝ 2 (ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
        ∀ w, 0 ≤ ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
            fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w ∧
          (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
              ≠ 0 →
            0 < ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
              fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w) := by
    intro p hp
    have hτa := (ProjPotDens.affLift_analyticAt hB x hx p hp).1
    have hτ1 : ∀ k, affCoord p (R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1) ⟨k, p k⟩ ≠ 0 := by
      intro k
      show R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ /
        R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0
      rw [hsx, div_self (hp k)]
      exact one_ne_zero
    have hC := (ProjPotDens.levi_fsMultiPot p hτ1 0).1
    refine ⟨hC.comp (f := fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x)
      (hτa.contDiffAt.restrict_scalars ℝ), fun w => ?_⟩
    rw [ReciprocityTheory.AnForm.levi_comp w hτa hC]
    obtain ⟨_, h1, h2⟩ := ProjPotDens.levi_fsMultiPot p hτ1
      (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w)
    exact ⟨h1, h2 fun k => ProjPotDens.fderiv_affLift_self hB x hx p hp w k⟩
  refine ⟨?_, fun hfull => ?_⟩
  · obtain ⟨p, hp⟩ : ∃ p : (k : K) → ι k, ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0 :=
      ⟨fun k => Classical.choose ((R.mem x.1 x.1 (R.mem_U x.1)).1 k),
        fun k => Classical.choose_spec ((R.mem x.1 x.1 (R.mem_U x.1)).1 k)⟩
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
      hessC_posSemidef _ _ hC fun w => (hl w).1
  · rw [hsx] at hfull
    obtain ⟨p, hp, j', hj', hr⟩ := hfull
    have hinj := ProjPotDens.injective_fderiv_affLift hB x p hp hx hj' hr
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    unfold ReciprocityTheory.AnForm.maDens
    refine mul_pos (mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
      (pow_pos (div_pos two_pos Real.pi_pos) _))
      (ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef _ fun _ => hessC_posDef _ _ hC fun w hw =>
        (hl w).2 fun h0 => hw (hinj (h0.trans (map_zero _).symm))).2
end ProjPotDens
end GroundTheory.Heights₂.Heights.Targets
