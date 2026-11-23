-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Cm_mul_Am
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:05.984031+00:00
-- url     : https://prove2.me/submissions/12fe032a-123c-46ca-ad58-552c77aa4421

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
private lemma Cm_mulVec_apply (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  simp only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : X.Cm u b τ * X.Am u τ = 0 := by
  ext i i'
  have e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i := rfl
  rw [e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]
  simp only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]
end ReciprocityTheory.ChartRestriction.G.FD.Data
