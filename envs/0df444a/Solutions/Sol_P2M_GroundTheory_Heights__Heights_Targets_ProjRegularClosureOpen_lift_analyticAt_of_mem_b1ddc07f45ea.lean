-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:10.909333+00:00
-- url     : https://prove2.me/submissions/4123f1a1-f89a-4413-b80d-6e20d43472c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
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
    AnalyticAt ℂ (fun v => R.lift x ((BV.chart j).symm v).1) u := by
  rw [analyticAt_pi_iff]
  intro p
  obtain ⟨k, hk⟩ : ∃ k, ((BV.chart j).symm u).1 ∈ (R.A.chart k).source := R.A.cover _
  have h1 : AnalyticAt ℂ ((fun y => R.lift x y p) ∘ (R.A.chart k).symm)
      (R.A.chart k ((BV.chart j).symm u).1) :=
    R.holo x p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k ((BV.chart j).symm u).1) ∈ R.U x
      rw [(R.A.chart k).left_inv hk]; exact hU⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) u :=
    hB.2 j k _ ⟨hu, hk⟩
  have hcont : ContinuousAt (fun v => ((BV.chart j).symm v).1) u :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hu)
  refine (h1.comp_of_eq h2 rfl).congr ?_
  filter_upwards [hcont.preimage_mem_nhds ((R.A.chart k).open_source.mem_nhds hk)] with v hv
  simp [(R.A.chart k).left_inv hv]
end GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
