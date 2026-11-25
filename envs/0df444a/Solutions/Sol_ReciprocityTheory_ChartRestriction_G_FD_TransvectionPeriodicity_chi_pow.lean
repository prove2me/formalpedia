-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.chi_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:57.68395+00:00
-- url     : https://prove2.me/submissions/28b58c3e-34a3-4d75-91a0-e530f7bd8828

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
theorem _root_.solution (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]
end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
