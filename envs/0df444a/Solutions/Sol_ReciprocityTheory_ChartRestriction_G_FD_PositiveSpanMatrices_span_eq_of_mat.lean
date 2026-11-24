-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.span_eq_of_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:38.387493+00:00
-- url     : https://prove2.me/submissions/009a03cc-0d46-4e2b-8732-e5e0d965b5af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f g : Fin n → V)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) (h : ∀ b, g b = ∑ b', A b' b • f b') :
    Submodule.span ℂ (Set.range g) = Submodule.span ℂ (Set.range f) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [h b]
    exact Submodule.sum_mem _ (fun b' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b', rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨b'', rfl⟩
    have hone : ∀ b', ∑ b, A⁻¹ b b'' * A b' b = (1 : Matrix (Fin n) (Fin n) ℂ) b' b'' := by
      intro b'
      rw [← Matrix.mul_nonsing_inv A hu, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    have key : f b'' = ∑ b, A⁻¹ b b'' • g b := by
      simp_rw [h, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hone, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
