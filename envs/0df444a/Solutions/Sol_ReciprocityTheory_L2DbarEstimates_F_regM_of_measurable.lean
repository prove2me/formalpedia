-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:19.136818+00:00
-- url     : https://prove2.me/submissions/b3611ee7-c5dd-42f0-80f8-ccdeb15f0dd1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_weakHolo
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ae_eq_eqOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_restrict_source


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (hReg : C.RegStatement) (hExt : ExtendStatement n M)
    (z : M → V n) (hz : IsLocalHomeomorph z) (F : M → ℂ) (hFm : Measurable F)
    (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    ∃ G : M → ℂ, Holo n z G ∧ F =ᵐ[vol n z] G := by
  have hU : ∀ e : OpenPartialHomeomorph M (V n), ∃ U : V n → ℂ, IsChart n z e →
      DifferentiableOn ℂ U e.target ∧ (F ∘ e.symm) =ᵐ[volume.restrict e.target] U := by
    intro e
    by_cases he : IsChart n z e
    · obtain ⟨U, h1, h2⟩ := hReg n e.target (F ∘ e.symm) e.open_target
        (regM_weakHolo hExt z hz e he F hFm hF hw)
      exact ⟨U, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose U hU using hU
  have hagree : ∀ e₁ e₂ : OpenPartialHomeomorph M (V n), IsChart n z e₁ → IsChart n z e₂ →
      ∀ x ∈ e₁.source ∩ e₂.source, U e₁ (z x) = U e₂ (z x) := by
    intro e₁ e₂ h₁ h₂ x hx
    have hWo : IsOpen (e₁.source ∩ e₂.source) := e₁.open_source.inter e₂.open_source
    set Ω := e₁.target ∩ e₁.symm ⁻¹' (e₁.source ∩ e₂.source) with hΩdef
    have hΩo : IsOpen Ω := e₁.isOpen_inter_preimage_symm hWo
    have hΩ1 : Ω ⊆ e₁.target := inter_subset_left
    have hkey : ∀ y ∈ Ω, e₂.symm y = e₁.symm y ∧ y ∈ e₂.target := by
      intro y hy
      have hw1 := hy.2.1
      have hw2 := hy.2.2
      have hy' : y = e₂ (e₁.symm y) := by
        rw [← h₂ hw2, h₁ hw1, e₁.right_inv hy.1]
      refine ⟨?_, ?_⟩
      · exact (congrArg e₂.symm hy').trans (e₂.left_inv hw2)
      · rw [hy']; exact e₂.map_source hw2
    have hΩ2 : Ω ⊆ e₂.target := fun y hy => (hkey y hy).2
    have heq := C.ae_eq_eqOn hΩo ((hU e₁ h₁).1.continuousOn.mono hΩ1)
      ((hU e₂ h₂).1.continuousOn.mono hΩ2) (by
        have a1 := ae_restrict_of_ae_restrict_of_subset hΩ1 (hU e₁ h₁).2
        have a2 := ae_restrict_of_ae_restrict_of_subset hΩ2 (hU e₂ h₂).2
        filter_upwards [a1, a2, ae_restrict_mem hΩo.measurableSet] with y hy1 hy2 hyΩ
        rw [← hy1, ← hy2]
        simp only [Function.comp_apply, (hkey y hyΩ).1])
    have hzx : z x ∈ Ω := by
      rw [h₁ hx.1]
      exact ⟨e₁.map_source hx.1, by simpa [e₁.left_inv hx.1] using hx⟩
    exact heq hzx
  choose ec hec hxc using exists_chart n z hz
  let G : M → ℂ := fun x => U (ec x) (z x)
  have hGe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ∀ y ∈ e.target, G (e.symm y) = U e y := by
    intro e he y hy
    have hs : e.symm y ∈ e.source := e.map_target hy
    show U (ec (e.symm y)) (z (e.symm y)) = U e y
    rw [hagree (ec (e.symm y)) e (hec _) he (e.symm y) ⟨hxc _, hs⟩, chart_z_symm n z e he y hy]
  have hG : Holo n z G := by
    intro e he
    exact (hU e he).1.congr (fun y hy => hGe e he y hy)
  have hGc : Continuous G := Smooth.continuous n z hz G (Holo.smooth n z G hG)
  refine ⟨G, hG, ?_⟩
  have hloc : ∀ x, ∀ᵐ y ∂(vol n z).restrict (ec x).source, F y = G y := by
    intro x
    rw [vol_restrict_source n z hz (ec x) (hec x),
      ae_map_iff ((ec x).continuousOn_symm.aemeasurable (ec x).open_target.measurableSet)
        (measurableSet_eq_fun hFm hGc.measurable)]
    filter_upwards [(hU (ec x) (hec x)).2, ae_restrict_mem (ec x).open_target.measurableSet]
      with y hy hyt
    rw [hGe (ec x) (hec x) y hyt]
    exact hy
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => (ec x).source)
    (fun x => (ec x).open_source)
  have hcov : (⋃ x ∈ T, (ec x).source) = univ := by
    rw [hTU]; exact eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hxc x⟩
  rw [EventuallyEq, ← Measure.restrict_univ (μ := vol n z), ← hcov,
    ae_restrict_biUnion_iff _ hTc]
  exact fun x _ => hloc x
end ReciprocityTheory.L2DbarEstimates.F
