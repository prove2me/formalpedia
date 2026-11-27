-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_smoothNear_chartPot_7acdc5ab859e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:12.712827+00:00
-- url     : https://prove2.me/submissions/75febc35-8431-4fb4-85e6-8f1df5e89915

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isOpen_chartLiftDom_f424c0a84590
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_chartLiftDom_of_coord_0b0f9f6d4975
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Set (Fin m → ℂ)}
    (hT : ∀ x ∈ T, x (σ.symm i) = 1) (j : Fin e) : SmoothNear T (chartPot σ i L j) := by
  refine ⟨chartLiftDom σ i, isOpen_chartLiftDom σ i, fun x hx => mem_chartLiftDom_of_coord (hT x hx), ?_⟩
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (L j).h (chartLift σ i x)) (chartLiftDom σ i) :=
    (hL j).comp (contDiff_chartLift σ i).contDiffOn fun _ hx => hx
  exact hh.log fun x hx => ((L j).pos _ hx).ne'
end GroundTheory.Heights₂.Heights
