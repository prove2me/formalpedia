-- Prove2me | solution 1 for UnipMove.DeltaValuation.posPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:14.193549+00:00
-- url     : https://prove2.me/submissions/86827a50-00b6-4892-a358-6e3ec1b95651

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left


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
    X.posPart x τ (c • v) = Complex.normSq c * X.posPart x τ v := by
  unfold Data.posPart
  simp only [hermC_smul_left, map_mul]
  have e : ∀ p q m : ℂ, c * p * m * (conj c * conj q) = (Complex.normSq c : ℂ) * (p * m * conj q) := by
    intro p q m
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]
end UnipMove.DeltaValuation
