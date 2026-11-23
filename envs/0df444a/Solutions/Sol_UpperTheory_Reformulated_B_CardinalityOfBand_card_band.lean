-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CardinalityOfBand.card_band
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:59.162003+00:00
-- url     : https://prove2.me/submissions/c731030d-d7e1-4bac-b59b-4a0aafed244b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardinalityOfBand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CardinalityOfBand
theorem _root_.solution :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
end UpperTheory.Reformulated.B.CardinalityOfBand
