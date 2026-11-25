-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:56.972566+00:00
-- url     : https://prove2.me/submissions/79f7fa7d-ee27-4383-ab5b-e065a51ed3cf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_loc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_sub_closure
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
theorem _root_.solution (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y := by
  classical
  have hext : ∀ i, ∃ g : V n → ℂ, DifferentiableOn ℂ g (A.chart i).target ∧
      ∀ u ∈ (A.chart i).target, fnG A w0 s De i u ≠ 0 → g u = F i ((A.chart i).symm u) := by
    intro i
    have hloc' : ∀ u ∈ (A.chart i).target, ∃ r > 0, Metric.ball u r ⊆ (A.chart i).target ∧
        ∃ U : V n → ℂ, DifferentiableOn ℂ U (Metric.ball u r) ∧
          Set.EqOn U (F i ∘ (A.chart i).symm) (Metric.ball u r \ {y | fnG A w0 s De i y = 0}) := by
      intro u hu
      obtain ⟨r, hr, hball, hint⟩ := fn_loc A hD hFs hloc i hu
      have hd1 : DifferentiableOn ℂ (fnG A w0 s De i) (Metric.ball u r) := (fn_diffG A hD i).mono hball
      have hd2 : DifferentiableOn ℂ (F i ∘ (A.chart i).symm) (Metric.ball u r \ {y | fnG A w0 s De i y = 0}) :=
        (hFs.1 i).mono fun y hy => ⟨hball hy.1, (fn_G_ne_iff A hD (hball hy.1)).1 hy.2⟩
      obtain ⟨U, hU1, hU2⟩ := hE u r (fnG A w0 s De i) (F i ∘ (A.chart i).symm) hd1 hd2 hint
      exact ⟨r, hr, hball, U, hU1, hU2⟩
    choose! r hr hball U hU1 hU2 using hloc'

    have hagree : ∀ u₀ ∈ (A.chart i).target, ∀ u ∈ (A.chart i).target,
        ∀ w ∈ Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀), U u w = U u₀ w := by
      intro u₀ hu₀ u hu w hw
      have hO : IsOpen (Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀)) := Metric.isOpen_ball.inter Metric.isOpen_ball
      have hOt : Metric.ball u (r u) ∩ Metric.ball u₀ (r u₀) ⊆ (A.chart i).target :=
        fun x hx => hball u hu hx.1
      have hcl := fn_sub_closure A hD hF i hO hOt
      refine Set.EqOn.of_subset_closure ?_ ((hU1 u hu).continuousOn.mono fun x hx => hx.1)
        ((hU1 u₀ hu₀).continuousOn.mono fun x hx => hx.2) Set.inter_subset_left hcl hw
      intro x hx
      rw [hU2 u hu ⟨hx.1.1, hx.2⟩, hU2 u₀ hu₀ ⟨hx.1.2, hx.2⟩]
    refine ⟨fun u => U u u, ?_, ?_⟩
    · intro u₀ hu₀
      have hd : DifferentiableAt ℂ (U u₀) u₀ :=
        (hU1 u₀ hu₀).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr u₀ hu₀)))
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr u₀ hu₀))] with u hu
      have hut : u ∈ (A.chart i).target := hball u₀ hu₀ hu
      exact hagree u₀ hu₀ u hut u ⟨Metric.mem_ball_self (hr u hut), hu⟩
    · intro u hu hG
      exact hU2 u hu ⟨Metric.mem_ball_self (hr u hu), hG⟩
  choose g hg1 hg2 using hext
  have hGF : ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → g i ((A.chart i) y) = F i y := by
    intro i y hyM hys
    have ht := (A.chart i).map_source hys
    rw [hg2 i _ ht (by rw [fn_G_ne_iff A hD ht, (A.chart i).left_inv hys]; exact hyM),
      (A.chart i).left_inv hys]
  have hGc : ∀ i, ContinuousOn (fun y => g i ((A.chart i) y)) (A.chart i).source := fun i =>
    (hg1 i).continuousOn.comp (A.chart i).continuousOn fun y hy => (A.chart i).map_source hy
  refine ⟨fun i y => g i ((A.chart i) y), ⟨fun i => ?_, fun i j y _ hyi hyj => ?_⟩, hGF⟩
  · refine ((hg1 i).mono Set.inter_subset_left).congr ?_
    intro u hu
    simp [Function.comp, (A.chart i).right_inv hu.1]
  · have hVo : IsOpen ((A.chart i).source ∩ (A.chart j).source) :=
      (A.chart i).open_source.inter (A.chart j).open_source
    have hgc : ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
      refine ((A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_).congr ?_
      · intro x hx
        exact ⟨(A.chart i).map_source hx.1, by rw [Set.mem_preimage, (A.chart i).left_inv hx.1]; exact hx.2⟩
      · intro x hx
        simp [Function.comp, (A.chart i).left_inv hx.1]
    have hcl := (fn_dense A hD hF).open_subset_closure_inter hVo
    refine Set.EqOn.of_subset_closure (f := fun y => g i ((A.chart i) y))
      (g := fun y => A.g la i j y * g j ((A.chart j) y)) ?_
      ((hGc i).mono Set.inter_subset_left) (hgc.mul ((hGc j).mono Set.inter_subset_right))
      Set.inter_subset_left hcl ⟨hyi, hyj⟩
    intro x hx
    simp only
    rw [hGF i x hx.2 hx.1.1, hGF j x hx.2 hx.1.2]
    exact hFs.2 i j x hx.2 hx.1.1 hx.1.2
end ReciprocityTheory.L2DbarEstimates.Y
