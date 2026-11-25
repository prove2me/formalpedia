-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.not_injective_of_trdeg_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:14.813206+00:00
-- url     : https://prove2.me/submissions/fe2fbbea-a4b7-42c1-be5c-9d7c6d75901c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {σ τ : Type}
    [Fintype σ] [Fintype τ] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ Ω) (n : ℕ)
    (hn : Algebra.trdeg K Ω = n) (hlt : n + Fintype.card τ < Fintype.card σ) :
    ¬ Function.Injective φ := by
  intro hinj
  have hai : AlgebraicIndependent K (φ ∘ fun i : σ => (MvPolynomial.X i : MvPolynomial σ K)) :=
    (MvPolynomial.algebraicIndependent_X σ K).map' hinj
  have hle := hai.cardinalMk_le_trdeg
  have h1 : Algebra.trdeg Ω (MvPolynomial τ Ω) = Cardinal.mk τ := by
    first
    | simpa using (MvPolynomial.trdeg_of_isDomain (R := Ω) (σ := τ))
    | simpa using (MvPolynomial.trdeg_of_isDomain Ω τ)
    | simpa using (MvPolynomial.trdeg (R := Ω) (σ := τ))
    | simpa using (Algebra.trdeg_mvPolynomial (R := Ω) (σ := τ))
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).lift_cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.algebraicIndependent_X τ Ω).isTranscendenceBasis_iff_isAlgebraic.mpr
        inferInstance).lift_cardinalMk_eq_trdeg.symm
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial τ Ω) =
      Algebra.trdeg K (MvPolynomial τ Ω) := by
    first
    | exact trdeg_add_eq K Ω
    | exact Algebra.trdeg_add_eq K Ω
  rw [← h2, hn, h1, Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
  have hc : Fintype.card σ ≤ n + Fintype.card τ := by exact_mod_cast hle
  omega
end ReciprocityTheory.ChartRestriction.G.T0
