-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.exists_stable_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:10.69906+00:00
-- url     : https://prove2.me/submissions/8c861448-4f24-4c38-8437-ae4f18048abe

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiStab

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
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution {K H : Type} [Field K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (I : Ideal H) : ∃ (k : ℕ) (e : H), IsIdempotentElem e ∧ I ^ k = Ideal.span {e} ∧ ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := isArtinian_of_tower K inferInstance
  haveI : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := H) (M := H)
    ⟨fun n => OrderDual.toDual (I ^ n), fun a b h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → I ^ j = I ^ n := fun j hj => congrArg OrderDual.ofDual (hn j hj).symm
  have hidem : IsIdempotentElem (I ^ n) := by
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hst (n + n) (by omega)
  obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem
  exact ⟨n, e, he, hI.trans Ideal.submodule_span_eq, hst⟩
end PositivityTheory.PrwZar.Qi
