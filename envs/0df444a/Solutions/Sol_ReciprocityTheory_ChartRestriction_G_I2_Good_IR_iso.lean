-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Good.IR_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:37.304462+00:00
-- url     : https://prove2.me/submissions/b8e8ae51-68ad-4110-aecd-62b1bebb4724

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private lemma Hf_add_left' {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]
private lemma Hf_add_right' {ι : Type} [Fintype ι] (v w w' : EuclideanSpace ℂ ι) :
    Hf v (w + w') = Hf v w + Hf v w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]
private lemma im_Hf_real_smul_left {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_assoc, ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])
private lemma Hf_real_smul_right_im {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, mul_left_comm _ (r : ℂ), ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_left_comm _ (r : ℂ), ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
namespace Good
theorem _root_.solution {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I) :
    ∀ v ∈ IR I, ∀ w ∈ IR I, (Hf v w).im = 0 := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add y y' _ _ h1 h2 => rw [Hf_add_right', Complex.add_im, h1, h2, add_zero]
    | smul r y _ h => rw [Hf_real_smul_right_im, h, mul_zero]
  | zero => simp [Hf]
  | add x x' _ _ h1 h2 => rw [Hf_add_left', Complex.add_im, h1, h2, add_zero]
  | smul r x _ h => rw [im_Hf_real_smul_left, h, mul_zero]
end Good
end ReciprocityTheory.ChartRestriction.G.I2
