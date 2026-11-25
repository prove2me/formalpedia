-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.aproj_eq_zero_of_Uz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:42.501696+00:00
-- url     : https://prove2.me/submissions/faafbabc-d37d-4317-b749-80b65d8d2de3

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
theorem _root_.solution {x : Frame X.Ψ r} {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz x ξ) :
    X.aproj x ξ u = 0 := by
  simp only [Data.Uz, Data.Iperp, Set.mem_setOf_eq] at hu
  obtain ⟨-, h2⟩ := hu
  funext τ
  have hH : X.Hf x τ (u τ) (Data.emb τ.1 ξ) = 0 := by
    have h3 := h2 τ
    simp only [Data.Jz, hermC_smul_left_dim] at h3
    rw [Data.Hf]
    exact (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
  simp only [Data.aproj, Data.lineV, hH, zero_div, zero_smul, Pi.zero_apply]
end UnipMove.AffineProjectionSplitting
