-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.aproj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:08.719882+00:00
-- url     : https://prove2.me/submissions/bf700940-3578-4e9a-843a-e693a13edb2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_AprojEqZeroOfUz
import Theorems.Thm_UnipMove_AffineProjectionSplitting_Hf_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open UnipMove.AffineProjectionSplitting
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)
namespace UnipMove.AffineProjectionSplitting
theorem _root_.solution (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.aproj x ξ (c • u) = c • X.aproj x ξ u := by
  funext τ
  simp only [Data.aproj, Data.lineV, Pi.smul_apply, Hf_smul, smul_smul, mul_div_assoc]
end UnipMove.AffineProjectionSplitting
