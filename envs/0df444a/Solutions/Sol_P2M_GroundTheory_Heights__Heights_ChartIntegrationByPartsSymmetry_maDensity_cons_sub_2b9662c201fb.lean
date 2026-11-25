-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_maDensity_cons_sub_2b9662c201fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:42.868018+00:00
-- url     : https://prove2.me/submissions/a7cc1a35-3350-4ef9-b441-06adc44bcf83

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hessC_sub_2ceea7e5a053
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution {f g : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDensity (Fin.cons (fun y => f y - g y) φ) z = maDensity (Fin.cons f φ) z - maDensity (Fin.cons g φ) z := by
  have hcons : ∀ h : (Fin (n + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons h φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
        (Fin.cons (hessC h z) fun i => hessC (φ i) z : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    intro h
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hsub : hessC (fun y => f y - g y) z = (1 : ℂ) • hessC f z + (-1 : ℂ) • hessC g z := by
    rw [hessC_sub hf hg z]
    simp [sub_eq_add_neg]
  have key := mdisc_cons_smul_add (1 : ℂ) (-1) (hessC f z) (hessC g z) fun i => hessC (φ i) z
  change ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc fun k => hessC ((Fin.cons (fun y => f y - g y) φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re =
    ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re -
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons g φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re
  rw [hcons, hcons, hcons, hsub, key]
  simp only [one_mul, neg_one_mul, Complex.add_re, Complex.neg_re]
  ring
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
