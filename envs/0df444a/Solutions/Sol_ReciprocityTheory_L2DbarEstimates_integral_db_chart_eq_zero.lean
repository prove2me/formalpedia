-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_db_chart_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:30:24.863486+00:00
-- url     : https://prove2.me/submissions/a740132a-19c7-48bd-85dd-916df5bf8b1c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_wdb_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_chart_extend
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_vol_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
private theorem d_db_eq_zero_of_not_mem_tsupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) :
    d n z j f x = 0 ∧ db n z j f x = 0 := by
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  rw [d_eq_wd n z e he j f x hxe, db_eq_wdb n z e he j f x hxe]
  have hzero : f ∘ e.symm =ᶠ[𝓝 (z x)] fun _ => 0 := by
    have h1 : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    rw [he hxe]
    have h2 : ∀ᶠ y in 𝓝 (e x), e.symm y ∈ (tsupport f)ᶜ :=
      (e.continuousAt_symm (e.map_source hxe)).preimage_mem_nhds (by rw [e.left_inv hxe]; exact h1)
    filter_upwards [h2] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := f) hy
  exact ⟨(wd_congr n j _ _ _ hzero).trans (wd_zero_fun n j _),
    (wdb_congr n j _ _ _ hzero).trans (wdb_zero_fun n j _)⟩
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (h : M → ℂ) (hh : Ck n z 1 h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ e.source) :
    ∫ x, db n z j h x ∂vol n z = 0 := by
  have hcont : Continuous (db n z j h) := Ck.continuous n z hz 0 _ (Ck.db n z 0 j h hh)
  have hzero : ∀ x, x ∉ e.source → db n z j h x = 0 := fun x hx =>
    (d_db_eq_zero_of_not_mem_tsupport n z hz j h x fun h' => hx (hs h')).2
  rw [integral_vol_chart n z hz e he _ hcont.measurable hzero]
  obtain ⟨H, hH1, hHc, hHt, hHo⟩ := chart_extend n z e he h hh hc hs
  have h1 : ∫ y in e.target, db n z j h (e.symm y) = ∫ y in e.target, wdb n j H y := by
    refine setIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
    rw [db_comp_symm n z e he j h y hy]
    exact wdb_congr n j _ _ y (hHt y hy).symm
  have h2 : ∫ y in e.target, wdb n j H y = ∫ y, wdb n j H y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    exact (wdb_congr n j _ _ y (hHo y hy)).trans (wdb_zero_fun n j y)
  rw [h1, h2, integral_wdb_eq_zero n j H hH1 hHc]
end ReciprocityTheory.L2DbarEstimates
