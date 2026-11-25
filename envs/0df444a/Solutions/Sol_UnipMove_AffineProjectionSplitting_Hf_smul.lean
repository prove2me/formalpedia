-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.Hf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:08.6838+00:00
-- url     : https://prove2.me/submissions/f1c777c1-880a-4451-9c5f-19d5c71e3f57

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
private lemma ppos_const_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  simp only [Data.ppos, hermC_smul_left_dim, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]
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
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by
  unfold Data.Hf
  rw [ppos_const_smul, smul_comm (2 : ℂ) c, ← smul_sub, hermC_smul_left_dim]
end UnipMove.AffineProjectionSplitting
