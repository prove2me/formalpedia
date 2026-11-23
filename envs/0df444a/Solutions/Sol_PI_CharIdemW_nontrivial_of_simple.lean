-- Prove2me | solution 1 for PI.CharIdemW.nontrivial_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.698902+00:00
-- url     : https://prove2.me/submissions/122d1315-70d1-4ce8-ac36-b73e515d309d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory
namespace PI.CharIdemW
open PI.CharIdem
section General
variable {G : Type} [Group G] [Fintype G]
private theorem nontrivial_of_simple_fdRep (W : FDRep ℂ G) [Simple W] : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero))
  have horth := FDRep.char_orthonormal W W
  have h0 : ∀ g : G, W.character g = 0 := fun g => by
    have hz : W.ρ g = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    show LinearMap.trace ℂ W (W.ρ g) = 0
    rw [hz, map_zero]
  have hne : Nonempty (W ≅ W) := ⟨Iso.refl W⟩
  simp [h0, hne] at horth
end General
end PI.CharIdemW
end

set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (W : FDRep ℂ G) [Simple W] : Nontrivial W := nontrivial_of_simple_fdRep W
end PI.CharIdemW
