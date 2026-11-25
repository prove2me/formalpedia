-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.open_convex_aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:11.706904+00:00
-- url     : https://prove2.me/submissions/b76d32e1-111a-42b5-9393-ec6aca50fa12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Finite κ] (a b : ι → κ → ℝ) :
    IsOpen {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} ∧
      Convex ℝ {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  constructor
  · have hs : {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} =
        ⋂ τ, ⋂ i, {y : ι → ℝ | 0 < a τ i + y τ * b τ i} := by
      ext y
      simp
    rw [hs]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add ((continuous_apply τ).mul continuous_const))
  · intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    intro τ i
    have h1 := hy τ i
    have h2 := hz τ i
    have key : a τ i + (s * y τ + t * z τ) * b τ i =
        s * (a τ i + y τ * b τ i) + t * (a τ i + z τ * b τ i) := by
      linear_combination (-(a τ i)) * hst
    rw [key]
    rcases hs.lt_or_eq with hs' | hs'
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h1) (mul_nonneg ht h2.le)
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using h2
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
