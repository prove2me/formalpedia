-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:31.47588+00:00
-- url     : https://prove2.me/submissions/a1e05e57-e70f-41af-89b1-0c92a4b285f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular

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
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegular
theorem _root_.solution {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ R.U x.1 := by
  obtain ⟨k, hk⟩ : ∃ k, x.1 ∈ (R.A.chart k).source := R.A.cover x.1
  have hxt : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hx
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hcont : ContinuousAt (fun u => ((BV.chart j).symm u).1) (BV.chart j x) :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hxt)
  have hev : ∀ s : Set R.X, IsOpen s → x.1 ∈ s →
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ s := fun s hs hxs =>
    hcont.preimage_mem_nhds (by
      show s ∈ 𝓝 ((BV.chart j).symm (BV.chart j x)).1
      rw [hsx]; exact hs.mem_nhds hxs)
  refine ⟨?_, hev _ (R.isOpen_U x.1) (R.mem_U x.1)⟩
  rw [analyticAt_pi_iff]
  intro p
  have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y p) ∘ (R.A.chart k).symm) (R.A.chart k x.1) :=
    R.holo x.1 p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k x.1) ∈ R.U x.1
      rw [(R.A.chart k).left_inv hk]; exact R.mem_U x.1⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) (BV.chart j x) :=
    hB.2 j k _ ⟨hxt, by
      show ((BV.chart j).symm (BV.chart j x)).1 ∈ (R.A.chart k).source
      rw [hsx]; exact hk⟩
  refine (h1.comp_of_eq h2 (by simp [hsx])).congr ?_
  filter_upwards [hev _ (R.A.chart k).open_source hk] with u hu
  simp [(R.A.chart k).left_inv hu]
end GroundTheory.Heights₂.Heights.Targets.ProjRegular
