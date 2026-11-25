-- Prove2me | solution 1 for P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:31.590476+00:00
-- url     : https://prove2.me/submissions/80fbd245-bfce-4302-b8d7-6bb529790a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAway
import Theorems.Thm_GlobalTheory_adjoin_mem_of_away_localization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Algebra
namespace GlobalTheory
theorem _root_.solution : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  intros R A R' A' _ _ _ _ _ _ _ _ _ _ _ g _ _ T b h
  exact GlobalTheory.adjoin_mem_of_away_localization g T b h
end GlobalTheory
