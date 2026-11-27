-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.isGlRep_factorAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:23.175672+00:00
-- url     : https://prove2.me/submissions/b481a222-860a-45dd-b51c-95b4b8d19107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (k : ℕ) (i : Fin k) : IsGlRep (n := n) (fun a b => factorAd (M := M) k i a b) := by
  intro a b c d
  ext F : 1
  refine big_ext fun κ => ?_
  rcases hx : κ i with ⟨x, y⟩
  have hz : ∀ p : Prop, ∀ _ : Decidable p, ∀ f : Module.End ℂ (Big n k M),
      ((if p then f else 0) F) κ = if p then f F κ else 0 := by
    intro p _ f; split_ifs <;> rfl
  simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hz, factorAd_apply,
    Function.update_self, Function.update_idem, hx]
  split_ifs <;> (try subst_vars) <;> (try contradiction) <;> abel
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
