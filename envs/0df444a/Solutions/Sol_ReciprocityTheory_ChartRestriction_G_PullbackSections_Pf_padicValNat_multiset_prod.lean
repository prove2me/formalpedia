-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.padicValNat_multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:41.993809+00:00
-- url     : https://prove2.me/submissions/f0ce4315-9f2b-45f5-9c07-03ae188dae16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] (s : Multiset ℕ) (h : ∀ x ∈ s, x ≠ 0) :
    padicValNat ℓ s.prod = (s.map (padicValNat ℓ)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    have hb : b ≠ 0 := h b (Multiset.mem_cons_self b s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl)
    rw [Multiset.prod_cons, padicValNat.mul hb hp, Multiset.map_cons, Multiset.sum_cons, ih hs]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
