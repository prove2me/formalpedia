-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qi42.open_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:40.121063+00:00
-- url     : https://prove2.me/submissions/0fdbc3db-ba7b-4d44-a614-e528be379b26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_OpenFix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi42
theorem _root_.solution :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by
  intro v inst H hH
  haveI : IsGalois ℚ_[v] (PadicAlgCl v) := IsAlgClosure.isGalois ℚ_[v] (PadicAlgCl v)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
end UpperTheory.Reformulated.B.Qi42
