-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:23.263037+00:00
-- url     : https://prove2.me/submissions/c98516d1-de7e-41f4-9412-671fed606c8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpolyStatement
import Theorems.Thm_GlobalTheory_LatOrb_exists_cyclicVector_of_separable_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable →
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  first | exact @GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | exact GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | (intros; apply GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly <;> assumption)
end _root_.GlobalTheory.T
