-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_proj_analyticAt_of_mem_ce35ab46931c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:14.034003+00:00
-- url     : https://prove2.me/submissions/bd602208-a7b1-4243-8d04-2b531f85fda6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
theorem _root_.solution {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((BV.chart j).symm v).1))) u := by
  classical
  have hF := lift_analyticAt_of_mem hB x hu hU
  have hs : AnalyticAt ℂ (fun v => segre (R.lift x ((BV.chart j).symm v).1)) u := by
    rw [analyticAt_pi_iff]
    intro i
    exact Finset.univ.analyticAt_fun_prod (fun k _ => analyticAt_pi_iff.1 hF ⟨k, i k⟩)
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hs
end GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
