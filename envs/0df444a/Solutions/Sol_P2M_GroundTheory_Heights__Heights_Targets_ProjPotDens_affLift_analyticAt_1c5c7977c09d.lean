-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:07:58.954781+00:00
-- url     : https://prove2.me/submissions/c9294a21-14dc-49ef-9743-a7ddf98cce44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDens
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d


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
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ∀ k, R.lift x.1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0 := by
  have hG := (ProjRegular.lift_analyticAt hB x hx).1
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ q, AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1 q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 hG q
  have hp' : ∀ k, R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0 := by
    rw [hsx]; exact hp
  refine ⟨?_, eventually_all.2 fun k => (hc ⟨k, p k⟩).continuousAt.eventually_ne (hp' k)⟩
  show AnalyticAt ℂ (fun u q => R.lift x.1 ((BV.chart j).symm u).1 q /
    R.lift x.1 ((BV.chart j).symm u).1 ⟨q.1, p q.1⟩) (BV.chart j x)
  exact AnalyticAt.pi fun q => (hc q).div (hc ⟨q.1, p q.1⟩) (hp' q.1)
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
