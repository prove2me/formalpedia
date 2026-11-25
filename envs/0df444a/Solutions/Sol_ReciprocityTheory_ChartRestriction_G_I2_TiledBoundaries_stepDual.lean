-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:20:24.715347+00:00
-- url     : https://prove2.me/submissions/590ab21d-e20e-4edb-bc87-235b24de3698

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepDual := by
  intro E _ _ X x hx
  classical
  choose! m hm using hx
  have hHadd : ∀ z y y' : Vsp X.dim, Hf z (y + y') = Hf z y + Hf z y' := by
    intro z y y'
    simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hHsub : ∀ z z' y : Vsp X.dim, Hf (z - z') y = Hf z y - Hf z' y := by
    intro z z' y
    simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hHsmul : ∀ (z : Vsp X.dim) (c : ℝ) (y : Vsp X.dim), (Hf z (c • y)).im = c * (Hf z y).im := by
    intro z c y
    simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.im_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hadd : ∀ y ∈ X.L, ∀ y' ∈ X.L, m (y + y') = m y + m y' := by
    intro y hy y' hy'
    have h1 := hm (y + y') (X.L.add_mem hy hy')
    have h2 := hm y hy
    have h3 := hm y' hy'
    rw [hHadd, Complex.add_im, h2, h3] at h1
    exact_mod_cast h1.symm
  obtain ⟨x', hx'L, hx'⟩ := X.perfect (AddMonoidHom.mk' (fun y : X.L => m y)
    (fun y y' => hadd y y.2 y' y'.2))
  set z := x - x' with hzdef
  have hz : ∀ y ∈ X.L, (Hf z y).im = 0 := by
    intro y hy
    have h1 := hx' ⟨y, hy⟩
    simp only [AddMonoidHom.mk'_apply] at h1
    rw [hzdef, hHsub, Complex.sub_im, hm y hy, h1, sub_self]
  let A : Vsp X.dim →+ ℝ := AddMonoidHom.mk' (fun y => (Hf z y).im)
    (fun y y' => by simp only [hHadd, Complex.add_im])
  have hA : ∀ y, (Hf z y).im = 0 := by
    intro y
    have h1 : (Hf z y).im = A y := rfl
    rw [h1, ← X.b.sum_repr y, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    show (Hf z (X.b.repr y i • X.b i)).im = 0
    rw [hHsmul, hz (X.b i) (Submodule.subset_span ⟨i, rfl⟩), mul_zero]
  have hI : (Hf z (Complex.I • z)).im = -∑ i, Complex.normSq (z i) := by
    simp only [Hf, PiLp.smul_apply, smul_eq_mul, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, Complex.conj_I, Complex.mul_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.neg_re, Complex.neg_im]
    ring
  have hsum : ∑ i, Complex.normSq (z i) = 0 := by
    have h1 := hA (Complex.I • z)
    rw [hI] at h1
    linarith
  have hz0 : z = 0 := by
    ext i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (z j))).mp hsum i
      (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp h1
  have hxx : x = x' := sub_eq_zero.mp hz0
  rw [hxx]
  exact hx'L
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
