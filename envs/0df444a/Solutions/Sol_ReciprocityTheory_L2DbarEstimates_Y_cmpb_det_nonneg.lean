-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpb_det_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:24.897946+00:00
-- url     : https://prove2.me/submissions/19a35334-6959-4d5e-b361-259862732296

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpbHessAtAddConst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder
namespace ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
universe u
variable {n : ℕ}
private theorem contDiffAt_ofReal_comp' {f : V n → ℝ} {x : V n} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) :
    ContDiffAt ℝ m (fun v => ((f v : ℝ) : ℂ)) x := by
  first
  | exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  | exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp)
  | fun_prop
private theorem fderiv_wdb_apply_of_hasFDerivAt_flip {g : V n → ℂ} {x : V n} (k : Fin n)
    (hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v) ((fderiv ℝ (fderiv ℝ g) x).flip v) x)
    (u : V n) : fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 := by
  have h3 := ((hlin (bas n k)).add ((hlin (Complex.I • bas n k)).const_mul Complex.I)).mul_const
    ((2 : ℂ)⁻¹)
  have hw : wdb n k g = fun y =>
      (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹ := by
    funext y
    simp only [wdb]
    ring
  rw [hw]
  first
  | rw [(show HasFDerivAt (𝕜 := ℝ) (fun y => (fderiv ℝ g y (bas n k) +
      Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹) _ x from h3).fderiv]
  | erw [h3.fderiv]
  simp [div_eq_mul_inv]
  try ring
section Atlas
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace WeightedAtlas
end WeightedAtlas
end Atlas
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
universe u
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    0 ≤ (cHess n (fun v => ((f v : ℝ) : ℂ)) x).det.re := by
  set g : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hgeq
  have hg2 : ContDiffAt ℝ 2 g x := contDiffAt_ofReal_comp' hf
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg2.fderiv_right (m := 1) (by first | exact one_add_one_eq_two.le | norm_num)).differentiableAt (by first | exact one_ne_zero | exact le_rfl)
  have hsym : ∀ u v : V n, fderiv ℝ (fderiv ℝ g) x u v = fderiv ℝ (fderiv ℝ g) x v u := by
    have hs : IsSymmSndFDerivAt ℝ g x := by
      first
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness])
      | exact hg2.isSymmSndFDerivAt le_rfl
    exact fun u v => hs u v
  have hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v)
      ((fderiv ℝ (fderiv ℝ g) x).flip v) x := by
    intro v
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    first
    | simpa using h
    | (convert h using 1; simp)
  have hval : ∀ u v : V n, fderiv ℝ (fun y => fderiv ℝ g y v) x u = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    rw [(hlin v).fderiv, ContinuousLinearMap.flip_apply]
  have hc1 : ∀ y v : V n, (starRingEnd ℂ) (fderiv ℝ g y v) = fderiv ℝ g y v := by
    intro y v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ g) y =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) := Complex.conjCLE.comp_fderiv
    have hg' : (Complex.conjCLE : ℂ → ℂ) ∘ g = g := by
      funext z; simp [hgeq]
    rw [hg'] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L v) e
    simpa using this.symm
  have hc2 : ∀ u v : V n, (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ g) x u v) = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ fun y => fderiv ℝ g y v) x =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun y => fderiv ℝ g y v) x) :=
      Complex.conjCLE.comp_fderiv
    have hh : (Complex.conjCLE : ℂ → ℂ) ∘ (fun y => fderiv ℝ g y v) = fun y => fderiv ℝ g y v := by
      funext z; simpa using hc1 z v
    rw [hh] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L u) e
    rw [← hval u v]
    simpa using this.symm
  have key : ∀ (k : Fin n) (u : V n), fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 :=
    fun k u => fderiv_wdb_apply_of_hasFDerivAt_flip k hlin u
  have hH : ∀ j k : Fin n, cHess n g x j k =
      (fderiv ℝ (fderiv ℝ g) x (bas n j) (bas n k) +
        fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k) +
        Complex.I * (fderiv ℝ (fderiv ℝ g) x (bas n j) (Complex.I • bas n k) -
          fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (bas n k))) / 4 := by
    intro j k
    simp only [cHess, Matrix.of_apply, wd, key]
    linear_combination (-(fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k)) / 4) *
      Complex.I_sq
  have hHerm : (cHess n g x).IsHermitian := by
    refine Matrix.IsHermitian.ext fun j k => ?_
    show (starRingEnd ℂ) (cHess n g x k j) = cHess n g x j k
    rw [hH k j, hH j k]
    simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_I, hc2, map_ofNat]
    linear_combination (1 / 4 : ℂ) * hsym (bas n k) (bas n j) +
      (1 / 4 : ℂ) * hsym (Complex.I • bas n k) (Complex.I • bas n j) -
      (Complex.I / 4) * hsym (bas n k) (Complex.I • bas n j) +
      (Complex.I / 4) * hsym (Complex.I • bas n k) (bas n j)
  have hq : ∀ v : Fin n → ℂ,
      dotProduct (star v) (Matrix.mulVec (cHess n g x) v) = leviV n g x (star v) := by
    intro v
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, starRingEnd_apply, star_star]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnn : ∀ v : Fin n → ℂ, 0 ≤ dotProduct (star v) (Matrix.mulVec (cHess n g x) v) := by
    intro v
    have him : (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).im = 0 := by
      first
      | simpa using hHerm.im_star_dotProduct_mulVec_self v
      | exact hHerm.im_star_dotProduct_mulVec_self v
    have hre : 0 ≤ (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).re := by
      rw [hq v]; exact hL (star v)
    exact Complex.le_def.2 ⟨by simpa using hre, by simpa using him.symm⟩
  have hPSD : (cHess n g x).PosSemidef := by
    first
    | exact ⟨hHerm, hnn⟩
    | exact ⟨hHerm, fun v => hnn v⟩
    | refine ⟨hHerm, fun v => ?_⟩
      have h := hnn ⇑v
      convert h using 1
      simp [Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hdet := hPSD.det_nonneg
  simpa using (Complex.le_def.1 hdet).1
end ReciprocityTheory.L2DbarEstimates.Y
