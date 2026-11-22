-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:46.976311+00:00
-- url     : https://prove2.me/submissions/47675107-c671-45ba-9e63-39b5fb219074

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeIffLtColH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk46
theorem _root_.solution :
    ∀ {r : Nat} {μ : Fin r → Int},
      @Antitone (Fin r) Int (@PartialOrder.toPreorder (Fin r) (@Fin.instPartialOrder r))
          (@PartialOrder.toPreorder Int
            (@ConditionallyCompletePartialOrderSup.toPartialOrder Int
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup Int
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder Int
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Int
                    Int.instConditionallyCompleteLinearOrder)))))
          μ →
        ∀ (c : Int) (m : Fin r),
          Iff (@LE.le Int Int.instLEInt c (μ m)) (@LT.lt Nat instLTNat (@Fin.val r m) (@UpperTheory.Reformulated.B.Qk46.colH r μ c)) := by
  intro r μ h c m
  unfold UpperTheory.Reformulated.B.Qk46.colH
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone h).symm
end UpperTheory.Reformulated.B.Qk46
