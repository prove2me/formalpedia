-- Prove2me | solution 1 for UnipMove.DeltaValuation.maj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:59:36.898137+00:00
-- url     : https://prove2.me/submissions/ce55b0fa-8187-409a-96db-6b389415ba74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply
import Theorems.Thm_UnipMove_DeltaValuation_posPart_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right


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
open UnipMove.DeltaValuation
namespace UnipMove.DeltaValuation
theorem _root_.solution {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  unfold Data.maj
  rw [posPart_smul, hermC_smul_left, hermC_smul_right]
  have e : c * (conj c * hermC τ.1 X.Gm v v) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm v v := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.re_ofReal_mul]
  ring
end UnipMove.DeltaValuation
