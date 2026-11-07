-- Prove2me | solution 1 for QEC.Coding.FiberBundle.nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:00.900198+00:00
-- url     : https://prove2.me/submissions/c3f14560-b936-4bcd-9300-4bada4d993de

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hProjection : homologyBaseProjection z ≠ 0) :
    Nonempty (SupportedHorizontalCell z) := by
  classical
  have hExists :
      ∃ x : Fin (4 * r) × ZMod (ell * ell),
        z (Sum.inl x) ≠ 0 := by
    by_contra hNot
    apply hProjection
    funext b
    change (∑ i : ZMod (ell * ell), z (Sum.inl (b, i))) = 0
    apply Finset.sum_eq_zero
    intro i _hi
    by_contra hi
    exact hNot ⟨(b, i), hi⟩
  rcases hExists with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩
end QEC.Coding.FiberBundle
