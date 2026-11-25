-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsB_psi_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:18.483686+00:00
-- url     : https://prove2.me/submissions/3ee840a5-107c-4338-8b17-c5b4efe24f55

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_O_open
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_O_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_det_diff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_inv_diffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psiC_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_psi_evEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviAt_log_normSq


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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
variable {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    0 ≤ A.leviAt i (bsPsi A w0 s mu0 σ) x ξ := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  rw [leviAt_congr A i _ _ x hi (bsB_psi_evEq A hD hF hσ hx hi)]
  have e1 : bsPsiC A w0 s mu0 σ i = fun y => (fun y => A.ph (mu0 - A.kap) i y +
      Real.log (‖(σ i y)⁻¹‖ ^ 2)) y + Real.log (‖(jz A w0 s i y).det‖ ^ 2) := rfl
  have E1 := leviAt_add A i (fun y => A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2))
    (fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) x ((h1.add h2).of_le hle) (h3.of_le hle) ξ
  have E2 := leviAt_add A i (A.ph (mu0 - A.kap) i) (fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) x
    (h1.of_le hle) (h2.of_le hle) ξ
  have hσx : σ i x ≠ 0 := bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx)
  have E3 := leviAt_log_normSq A i (fun y => (σ i y)⁻¹) x hi (by
      filter_upwards [hO.mem_nhds hxO] with v hv
      exact (bsB_inv_diffOn A hσ i).differentiableAt (hO.mem_nhds hv)) (inv_ne_zero hσx) ξ
  have E4 := leviAt_log_normSq A i (fun y => (jz A w0 s i y).det) x hi (bsB_det_diff A hD hF hx hi)
      (jz_det_ne A hD hF x hx i hi) ξ
  have E5 := hpos i x hi ξ
  simp only [add_zero] at E5
  rw [e1]
  beta_reduce at E1 E2 E3 E4 ⊢
  linarith
end ReciprocityTheory.L2DbarEstimates.Y
