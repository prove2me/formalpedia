-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:36.528493+00:00
-- url     : https://prove2.me/submissions/3b6ae601-8399-4031-ac32-8219a4cbf3cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffG
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_G_ne_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_not_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ident
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) : Dense (A.Mset w0 s De) := by
  have key : interior (A.Mset w0 s De)ᶜ = ∅ := by
    have hWc : IsClosed (interior (A.Mset w0 s De)ᶜ) := by
      rw [← closure_subset_iff_isClosed]
      intro y hy
      have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
      have hv : A.chart (A.pick y) y ∈ (A.chart (A.pick y)).target := (A.chart _).map_source hys
      obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
      have hNo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
          Metric.ball (A.chart (A.pick y) y) r) :=
        (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
      have hyN : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
          Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Metric.mem_ball_self hr⟩
      obtain ⟨y', hy'N, hy'W⟩ := mem_closure_iff.1 hy _ hNo hyN
      have hv'B := hy'N.2
      have hev : fnG A w0 s De (A.pick y) =ᶠ[𝓝 (A.chart (A.pick y) y')] 0 := by
        have ht := ((A.chart (A.pick y)).continuousAt_symm (hB hv'B)).tendsto
        rw [(A.chart _).left_inv hy'N.1] at ht
        have h1 := ht.eventually (isOpen_interior.mem_nhds hy'W)
        filter_upwards [h1, (A.chart _).open_target.mem_nhds (hB hv'B)] with v hv1 hv2
        have := (fn_G_ne_iff A hD (De := De) hv2).not.2 (interior_subset hv1)
        simpa using this
      have hz := C.ident n _ _ _ Metric.isOpen_ball (convex_ball _ _)
        ((fn_diffG A hD (De := De) (A.pick y)).mono hB) hv'B hev
      refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (hNo.mem_nhds hyN) fun x hx => ?_)
      have h2 := hz hx.2
      have := (fn_G_ne_iff A hD (De := De) ((A.chart _).map_source hx.1)).not.1 (by simpa using h2)
      rwa [(A.chart _).left_inv hx.1] at this
    by_contra hne
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨P, hP, hPc⟩ := hD.meets y
    have hPW := (IsClopen.connectedComponent_subset ⟨hWc, isOpen_interior⟩ hy) hPc
    exact fn_not_ev A hD hF hP (mem_interior_iff_mem_nhds.1 hPW)
  have := interior_eq_empty_iff_dense_compl.1 key
  rwa [compl_compl] at this
end ReciprocityTheory.L2DbarEstimates.Y
