-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:27:46.248057+00:00
-- url     : https://prove2.me/submissions/a7dff5cb-0ed1-43b6-9a70-740c76997051

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (g : (K →+* ℂ) → ℝ) :
    ∑ φ : K₁ →+* ℂ, g (φ.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => φ.comp (algebraMap K K₁)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  norm_cast
  letI : Algebra K ℂ := τ.toAlgebra
  let eqv : {φ : K₁ →+* ℂ // φ.comp (algebraMap K K₁) = τ} ≃ (K₁ →ₐ[K] ℂ) :=
    { toFun := fun φ => { φ.1 with commutes' := fun r => RingHom.congr_fun φ.2 r }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun r => ψ.commutes r⟩
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr eqv, AlgHom.card]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
