-- Prove2me | solution 1 for UnipMove.GraphH.span_cols_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:47.071133+00:00
-- url     : https://prove2.me/submissions/883913db-adaf-48fb-b5e1-a23a9da59f1b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution {p : ℕ} (u w : Fin p → Fin r → ℂ) (A : Matrix (Fin p) (Fin p) ℂ)
    (hA : IsUnit A.det) (h : ∀ a, u a = ∑ b, A b a • w b) :
    Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by
  have key : ∀ b, w b = ∑ a, A⁻¹ a b • u a := by
    intro b
    have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hc : ∀ c, ∑ a, A⁻¹ a b * A c a = (1 : Matrix (Fin p) (Fin p) ℂ) c b := by
      intro c
      rw [← hinv, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc, Matrix.one_apply]
    simp
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [key b]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end UnipMove.GraphH
