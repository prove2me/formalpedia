-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:36.118135+00:00
-- url     : https://prove2.me/submissions/0f823587-12dc-40e6-9253-8107e3e5b854

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_trT_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
theorem _root_.solution [FiniteDimensional K K₂] [Algebra.IsSeparable K K₂] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K K₂) (w : K₂ ⊗[K] V) :
    w = ∑ i, ((Algebra.traceForm K K₂).dualBasis
      (traceForm_nondegenerate (K := K) (L := K₂)) b i) • ((1 : K₂) ⊗ₜ[K] trT (b i • w)) := by
  set d := (Algebra.traceForm K K₂).dualBasis (traceForm_nondegenerate (K := K) (L := K₂)) b
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    have hx : x = ∑ i, Algebra.trace K K₂ (b i * x) • d i := by
      conv_lhs => rw [← d.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
    conv_lhs => rw [hx]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, trT_tmul]
    exact TensorProduct.smul_tmul _ _ _
  | add y z hy hz =>
    simp only [smul_add, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
