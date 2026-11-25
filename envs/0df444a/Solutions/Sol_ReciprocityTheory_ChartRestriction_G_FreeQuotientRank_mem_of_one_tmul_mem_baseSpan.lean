-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.mem_of_one_tmul_mem_baseSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:49.554738+00:00
-- url     : https://prove2.me/submissions/e055ba50-5b1d-4124-9da7-d4f2facddecc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_mem_baseSpan_iff


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
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) {v : V}
    (h : (1 : F) ⊗ₜ[K] v ∈ baseSpan F U) : v ∈ U := by
  rw [mem_baseSpan_iff] at h
  simp only [LinearMap.lTensor_tmul, Submodule.mkQ_apply] at h
  have hinj : Function.Injective (fun q : V ⧸ U => (1 : F) ⊗ₜ[K] q) := by
    have h1 : Function.Injective (LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K F).injective
    intro q q' hq
    have : LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q) =
        LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q') := by
      simpa using hq
    have := h1 this
    simpa using congrArg (TensorProduct.lid K (V ⧸ U)) this
  have : (Submodule.Quotient.mk v : V ⧸ U) = 0 := hinj (by simpa using h)
  exact (Submodule.Quotient.mk_eq_zero U).mp this
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
