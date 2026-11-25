-- Prove2me | solution 1 for UpperTheory.V.prime_of_mem_Bchi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:52.437136+00:00
-- url     : https://prove2.me/submissions/613084bf-27e2-40d3-be54-f02047f24246

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
theorem _root_.solution {ψ : PChar} {l : ℕ} (h : l ∈ Bchi ψ) : l.Prime ∧ l ≠ 2 := by
  unfold Bchi at h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact ⟨Nat.prime_three, by decide⟩
  · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
    exact ⟨Nat.prime_of_mem_primeFactors hmem, hne⟩
end UpperTheory.V
