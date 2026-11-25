-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.emb_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:04.417977+00:00
-- url     : https://prove2.me/submissions/6bd87550-6e50-48b5-8cff-bd2adbf649c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b


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
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
theorem _root_.solution (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
