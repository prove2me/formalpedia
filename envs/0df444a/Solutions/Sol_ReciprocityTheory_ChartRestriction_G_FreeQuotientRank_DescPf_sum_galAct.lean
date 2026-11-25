-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.sum_galAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:41.103007+00:00
-- url     : https://prove2.me/submissions/ddd5786b-9c01-443a-9216-de5f4efcc71d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_trT_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_DescPf_galAct_tmul

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
theorem _root_.solution [FiniteDimensional K K₂] [IsGalois K K₂] (y : K₂ ⊗[K] V) :
    ∑ σ : K₂ ≃ₐ[K] K₂, galAct σ y = (1 : K₂) ⊗ₜ[K] trT y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    simp only [galAct_tmul, trT_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add y z hy hz =>
    simp only [map_add, Finset.sum_add_distrib, hy, hz, TensorProduct.tmul_add]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
