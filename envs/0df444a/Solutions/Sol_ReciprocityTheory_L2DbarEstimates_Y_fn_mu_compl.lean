-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_mu_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:51.950649+00:00
-- url     : https://prove2.me/submissions/17a9a290-334c-4a7c-9b25-f7bd7d34e91a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_G_ne_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_dense
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffG
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
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
theorem _root_.solution (hN : EXTNullStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    A.mu (A.Mset w0 s De)ᶜ = 0 := by
  apply measure_null_of_locally_null
  intro x _
  have hxs : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hxt : (A.chart (A.pick x)) x ∈ (A.chart (A.pick x)).target := (A.chart (A.pick x)).map_source hxs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _ hxt
  have hGd : DifferentiableOn ℂ (fnG A w0 s De (A.pick x)) (Metric.ball ((A.chart (A.pick x)) x) r) :=
    (fn_diffG A hD (A.pick x)).mono hball
  have hO1 : IsOpen ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r) :=
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source Metric.isOpen_ball
  have hB2 : IsOpen (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ) :=
    hGd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hO2 : IsOpen ((A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹'
      (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ)) :=
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source hB2
  have hne : ∃ y ∈ Metric.ball ((A.chart (A.pick x)) x) r, fnG A w0 s De (A.pick x) y ≠ 0 := by
    obtain ⟨y, ⟨hys, hyB⟩, hyM⟩ := (fn_dense A hD hF).inter_open_nonempty _ hO1
      ⟨x, hxs, Metric.mem_ball_self hr⟩
    refine ⟨(A.chart (A.pick x)) y, hyB, ?_⟩
    rw [fn_G_ne_iff A hD ((A.chart (A.pick x)).map_source hys), (A.chart (A.pick x)).left_inv hys]
    exact hyM
  have hZ : volume (Metric.ball ((A.chart (A.pick x)) x) r ∩ {v | fnG A w0 s De (A.pick x) v = 0}) = 0 :=
    hN _ _ _ hGd hne
  set T := ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r) \
      ((A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹'
        (Metric.ball ((A.chart (A.pick x)) x) r ∩ fnG A w0 s De (A.pick x) ⁻¹' {0}ᶜ)) with hTdef
  have hTm : MeasurableSet T := hO1.measurableSet.diff hO2.measurableSet
  have hvol : volume ((A.chart (A.pick x)) '' T) = 0 := by
    refine measure_mono_null ?_ hZ
    rintro v ⟨y, hyT, rfl⟩
    refine ⟨hyT.1.2, ?_⟩
    by_contra hG
    exact hyT.2 ⟨hyT.1.1, hyT.1.2, hG⟩
  have hTnull : A.mu T = 0 := by
    rw [A.mu_chart (A.pick x) T hTm (fun y hy => hy.1.1)]
    first
      | exact setLIntegral_measure_zero _ _ hvol
      | simp [Measure.restrict_eq_zero.2 hvol]
  refine ⟨(A.Mset w0 s De)ᶜ ∩ ((A.chart (A.pick x)).source ∩
      (A.chart (A.pick x)) ⁻¹' Metric.ball ((A.chart (A.pick x)) x) r),
    inter_mem_nhdsWithin _ (hO1.mem_nhds ⟨hxs, Metric.mem_ball_self hr⟩), ?_⟩
  refine measure_mono_null ?_ hTnull
  rintro y ⟨hyM, hys, hyB⟩
  refine ⟨⟨hys, hyB⟩, ?_⟩
  rintro ⟨_, _, hG⟩
  apply hyM
  have := (fn_G_ne_iff A hD ((A.chart (A.pick x)).map_source hys)).1 hG
  rwa [(A.chart (A.pick x)).left_inv hys] at this
end ReciprocityTheory.L2DbarEstimates.Y
