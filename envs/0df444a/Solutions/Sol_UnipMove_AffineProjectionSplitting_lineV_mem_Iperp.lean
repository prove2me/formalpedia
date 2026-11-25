-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.lineV_mem_Iperp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:49:46.589899+00:00
-- url     : https://prove2.me/submissions/2b5b4687-a046-43bc-a6ec-6cb722a8bade

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_AprojEqZeroOfUz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace AffineProjectionSplitting
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)
private lemma hermC_smul_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (u v : Fin n → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private lemma hermC_emb_emb_eq_herm {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
end AffineProjectionSplitting
end
end UnipMove
end

set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open UnipMove.AffineProjectionSplitting
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)
namespace UnipMove.AffineProjectionSplitting
theorem _root_.solution (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) : X.lineV ξ s ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq]
  intro τ
  simp only [Data.lineV, hermC_smul_left_dim, hermC_emb_emb_eq_herm, hξ, map_zero, mul_zero]
end UnipMove.AffineProjectionSplitting
