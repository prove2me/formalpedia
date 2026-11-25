-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_isOpen_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:33.296576+00:00
-- url     : https://prove2.me/submissions/065ed3cd-e4a1-467e-98fc-ec749b2fcd07

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_denominator_ne_zero_on_set
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (i : ι) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have secS : ∀ k i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      s k i y = A.g L i j y * s k j y := by
    intro k i j y hi hj
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have secW : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source →
      w0 i y = A.g L i j y * w0 j y := by
    intro i j y hi hj
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    exact hs.2 i j y trivial hi hj
  have hw : DifferentiableOn ℂ (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have hs := hD.isSection_denom
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  have hsk : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm) (A.chart i).target := by
    intro k
    have hs := hD.sec_s k
    unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hs
    simpa using hs.1 i
  set O1 := (A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ with hO1def
  have hO1 : IsOpen O1 := hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target
    isOpen_compl_singleton
  have hzd : ∀ k, DifferentiableOn ℂ (fun v => (A.zLoc w0 s i v).ofLp k) O1 := by
    intro k
    have h1 : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) O1 :=
      (hsk k).mono Set.inter_subset_left
    have h2 : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) O1 :=
      hw.mono Set.inter_subset_left
    have h3 := h1.mul (h2.inv fun v (hv : v ∈ O1) => hv.2)
    refine h3.congr fun v _ => ?_
    simp [WeightedAtlas.zLoc, div_eq_mul_inv]
  have hset : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De =
      O1 ∩ (fun v => MvPolynomial.eval (fun k => A.zLoc w0 s i v k) De) ⁻¹' {0}ᶜ := by
    ext v
    constructor
    · rintro ⟨hv, hM⟩
      refine ⟨⟨hv, denominator_ne_zero_on_set A hD hM i ((A.chart i).map_target hv)⟩, ?_⟩
      show MvPolynomial.eval _ De ≠ 0
      rw [fc_zLoc_eq A hD i v hv]
      exact hM.2
    · rintro ⟨⟨hv, hw0⟩, hev⟩
      refine ⟨hv, ?_, ?_⟩
      · intro h0
        apply hw0
        show w0 i ((A.chart i).symm v) = 0
        rw [secW i (A.pick _) _ ((A.chart i).map_target hv) (A.mem_pick _), h0, mul_zero]
      · have h1 : MvPolynomial.eval (fun k => A.zLoc w0 s i v k) De ≠ 0 := hev
        rw [fc_zLoc_eq A hD i v hv] at h1
        exact h1
  rw [hset]
  have hc : ContinuousOn (fun v => fun k => A.zLoc w0 s i v k) O1 :=
    continuousOn_pi.mpr fun k => (hzd k).continuousOn
  exact ((MvPolynomial.continuous_eval De).comp_continuousOn hc).isOpen_inter_preimage hO1
    isOpen_compl_singleton
end ReciprocityTheory.L2DbarEstimates.Y
