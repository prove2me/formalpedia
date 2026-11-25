-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_db_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:37.824807+00:00
-- url     : https://prove2.me/submissions/eb1f8a36-9220-45d3-9b8f-6df75d357943

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_zero_fun
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart

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
private theorem wd_wdb_mul {n : ℕ} {u v : V n → ℂ} {y : V n} (hu : DifferentiableAt ℝ u y)
    (hv : DifferentiableAt ℝ v y) (j : Fin n) :
    wd n j (fun w => u w * v w) y = wd n j u y * v y + u y * wd n j v y ∧
      wdb n j (fun w => u w * v w) y = wdb n j u y * v y + u y * wdb n j v y := by
  have hF : fderiv ℝ (fun w => u w * v w) y = u y • fderiv ℝ v y + v y • fderiv ℝ u y :=
    (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  constructor <;>
    simp only [wd, wdb, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] <;> ring
private theorem d_db_mul_of_ck_one {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y * g y) x = d n z j f x * g x + f x * d n z j g x ∧
      db n z j (fun y => f y * g y) x = db n z j f x * g x + f x * db n z j g x := by
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hxe]; exact e.open_target.mem_nhds (e.map_source hxe)
  have du : DifferentiableAt ℝ (f ∘ e.symm) (z x) :=
    ((hf e he).contDiffAt hT).differentiableAt one_ne_zero
  have dv : DifferentiableAt ℝ (g ∘ e.symm) (z x) :=
    ((hg e he).contDiffAt hT).differentiableAt one_ne_zero
  have hx' : e.symm (z x) = x := by rw [he hxe, e.left_inv hxe]
  rw [d_eq_wd n z e he j _ x hxe, d_eq_wd n z e he j f x hxe, d_eq_wd n z e he j g x hxe,
    db_eq_wdb n z e he j _ x hxe, db_eq_wdb n z e he j f x hxe, db_eq_wdb n z e he j g x hxe]
  have key := wd_wdb_mul du dv j
  simp only [Function.comp_apply, hx'] at key
  exact key
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j f x * g x ∂vol n z = -∫ x, f x * db n z j g x ∂vol n z := by
  have hfg1 : Ck n z 1 (fun y => f y * g y) := fun e he => (hf e he).mul (hg e he)
  have h0 := integral_db_eq_zero n z hz j (fun y => f y * g y) hfg1 hc.mul_left
  have dcs : HasCompactSupport (db n z j g) := hc.mono' fun x hx => by
    by_contra hx'
    exact hx (d_db_eq_zero_of_not_mem_tsupport n z hz j _ x hx').2
  have i1 : Integrable (fun x => db n z j f x * g x) (vol n z) :=
    integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 j f hf)).mul (Ck.continuous n z hz 1 g hg)) hc.mul_left
  have i2 : Integrable (fun x => f x * db n z j g x) (vol n z) :=
    integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 1 f hf).mul (Ck.continuous n z hz 0 _ (Ck.db n z 0 j g hg))) dcs.mul_left
  have hprod : (fun x => db n z j (fun y => f y * g y) x) =
      fun x => db n z j f x * g x + f x * db n z j g x :=
    funext fun x => (d_db_mul_of_ck_one n z hz f g hf hg j x).2
  rw [hprod, integral_add i1 i2] at h0
  linear_combination h0
end ReciprocityTheory.L2DbarEstimates
