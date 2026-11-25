-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_weakHolo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:09.343904+00:00
-- url     : https://prove2.me/submissions/326b275c-1e51-461c-b1e9-6fef295cdc59

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_dbarDir_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_db_eq_zero_of_notMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_locInt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_vol_chart


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
theorem _root_.solution {n : ℕ} (hExt : ExtendStatement n M) (z : M → V n)
    (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (F : M → ℂ) (hFm : Measurable F) (hF : LocalL2Isometry (vol n z) F)
    (hw : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) :
    C.WeakHolo e.target (F ∘ e.symm) := by
  have hli := regM_locInt z hz e he F hFm hF
  refine ⟨hli, fun g hg v => ?_⟩
  obtain ⟨hgs, hgc, hgt⟩ := hg
  obtain ⟨hφs, hφc, hφt, hφd⟩ := hExt z hz e g he hgs hgc hgt
  have hj : ∀ j, ∫ y in e.target, F (e.symm y) * wdb n j g y = 0 := by
    intro j
    have h0 := hw _ ⟨hφs, hφc⟩ j
    have hdbc := Smooth.continuous n z hz _ (Smooth.db n z j _ hφs)
    rw [integral_vol_chart n z hz e he (fun x => F x * db n z j _ x) (hFm.mul hdbc.measurable)
      (fun x hx => by
        rw [regM_db_eq_zero_of_notMem z j _ x (fun h => hx (hφt h)), mul_zero])] at h0
    rw [← h0]
    refine setIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)
    rw [(hφd j (e.symm y) (e.map_target hy)).2, e.right_inv hy]
  have hD : Continuous (fderiv ℝ g) := hgs.continuous_fderiv (by simp)
  have hint : ∀ j, IntegrableOn (fun y => F (e.symm y) * wdb n j g y) e.target := by
    intro j
    have hwc : Continuous (wdb n j g) := by
      unfold wdb
      exact ((hD.clm_apply continuous_const).add
        (continuous_const.mul (hD.clm_apply continuous_const))).div_const 2
    refine ((hli.integrableOn_compact_subset hgt hgc).mul_continuousOn hwc.continuousOn
      hgc).of_forall_sdiff_eq_zero e.open_target.measurableSet (fun y hy => ?_)
    have h0 : fderiv ℝ g y = 0 :=
      Function.notMem_support.mp (fun h => hy.2 (support_fderiv_subset ℝ h))
    simp [wdb, h0]
  calc ∫ y in e.target, (F ∘ e.symm) y * C.dbarDir g y v
      = ∫ y in e.target, ∑ j, (-2 * Complex.I * conj (v j)) * (F (e.symm y) * wdb n j g y) := by
        refine setIntegral_congr_fun e.open_target.measurableSet (fun y _ => ?_)
        simp only [Function.comp_apply, regM_dbarDir_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, ∫ y in e.target, (-2 * Complex.I * conj (v j)) * (F (e.symm y) * wdb n j g y) :=
        integral_finsetSum _ (fun j _ => (hint j).const_mul _)
    _ = 0 := by simp only [integral_const_mul, hj, mul_zero, Finset.sum_const_zero]
end ReciprocityTheory.L2DbarEstimates.F
