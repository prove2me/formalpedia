-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.Iperp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:12.799945+00:00
-- url     : https://prove2.me/submissions/1d06722c-2169-4444-ba98-12d42bc7216b

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
private lemma hermC_sub_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u w v : Fin n → ℂ) : hermC τ G (u - w) v = hermC τ G u v - hermC τ G w v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
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
theorem _root_.solution {u w : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) (hw : w ∈ X.Iperp ξ) :
    u - w ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu hw ⊢
  intro τ
  rw [Pi.sub_apply, hermC_sub_left_dim, hu τ, hw τ, sub_zero]
end UnipMove.AffineProjectionSplitting
