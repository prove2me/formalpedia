-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.lintegral_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:25.439554+00:00
-- url     : https://prove2.me/submissions/468c05f2-5efe-421c-a707-a2bd2e35f337

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mu_piece
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_rho_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isOpen_Mset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart


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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (φ : Y → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y in A.Mset w0 s De, φ y ∂A.mu =
      ∫⁻ x : A.Mset w0 s De, φ x * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick x) x) /
        ‖(jz A w0 s (A.pick x) x).det‖ ^ 2) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  have hmeas : A.mu.comap Subtype.val =
      (vol n (flatStein A hD hF).z).withDensity fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) := by
    choose e he hxe using fun x : A.Mset w0 s De => exists_chart n _ hz x
    let U : A.Mset w0 s De → Set (A.Mset w0 s De) := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hUo : ∀ x, IsOpen (U x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have huniv : ⋃ t : T, U t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, U i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hUo t).measurableSet)]
    exact fc_mu_piece A hD hF (e t) (he t) (A.pick (t : Y)) (B ∩ U t)
      (hB.inter (hUo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hMm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)
end ReciprocityTheory.L2DbarEstimates.Y
