-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:24.231641+00:00
-- url     : https://prove2.me/submissions/830831a3-e408-42d0-9045-fddf32ded3e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
theorem _root_.solution (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    conj (hermC τ G u v) = hermC τ G v u := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc' τ (G b a), hG]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
