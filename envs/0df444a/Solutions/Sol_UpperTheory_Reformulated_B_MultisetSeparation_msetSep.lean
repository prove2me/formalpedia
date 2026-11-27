-- Prove2me | solution 1 for UpperTheory.Reformulated.B.MultisetSeparation.msetSep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:43.385656+00:00
-- url     : https://prove2.me/submissions/c105d764-2dd1-48f3-b4d0-86e0baf24a7d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultisetSeparation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial in
private lemma eval_prod_add (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod).eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, ih, eval_sub, eval_X, eval_C]
    ring
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.MultisetSeparation
theorem _root_.solution :
    ∀ (m m' : Multiset ℂ),
    (∀ (u : ℂ), (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod) → m = m' := by
  intro m m' h
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_add, eval_prod_add, h u]
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
end UpperTheory.Reformulated.B.MultisetSeparation
