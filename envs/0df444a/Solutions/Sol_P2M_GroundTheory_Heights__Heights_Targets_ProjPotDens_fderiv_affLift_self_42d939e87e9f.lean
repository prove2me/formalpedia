-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_fderiv_affLift_self_42d939e87e9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:59.159813+00:00
-- url     : https://prove2.me/submissions/8f573010-4361-4b88-a31d-e523d6a6ecb4

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) (w : Fin n → ℂ) (k : K) :
    fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
      ⟨k, p k⟩ = 0 := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have h1 := hasFDerivAt_pi'.1 hτa.differentiableAt.hasFDerivAt ⟨k, p k⟩
  have h2 : HasFDerivAt (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1) ⟨k, p k⟩)
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) (BV.chart j x) :=
    (hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq (by
      filter_upwards [hev] with u hu
      exact div_self (hu k))
  have := congrArg (fun L => L w) (h1.unique h2)
  simpa using this
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
