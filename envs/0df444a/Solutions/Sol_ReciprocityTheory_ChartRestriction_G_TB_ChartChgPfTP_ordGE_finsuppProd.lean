-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_finsuppProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:50.232101+00:00
-- url     : https://prove2.me/submissions/0bab90aa-bf56-4b3b-970b-336e380c9dff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ordGE_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ τ : Type} (A : τ → MvPowerSeries σ k) (hA : ∀ s, OrdGE 1 (A s)) (dd : τ →₀ ℕ) :
    OrdGE dd.degree (dd.prod fun s n => A s ^ n) := by
  classical
  have key : ∀ S : Finset τ, OrdGE (∑ s ∈ S, dd s) (∏ s ∈ S, A s ^ dd s) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp only [Finset.sum_empty, Finset.prod_empty]
      exact ordGE_zero_left _
    · intro a S ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ordGE_mul (ordGE_pow (hA a) _) ih
  first
  | exact key dd.support
  | (unfold Finsupp.prod Finsupp.degree; exact key _)
  | (rw [Finsupp.prod, Finsupp.degree]; exact key _)
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
