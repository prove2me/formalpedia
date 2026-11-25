-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.exists_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:14.535128+00:00
-- url     : https://prove2.me/submissions/c36d933b-9e8f-4cdb-8bf1-2850e08680bd

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by
  obtain ⟨a, ha, hav⟩ := hsp (Pi.single j 1)
  have hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1) := by
    intro i hi
    have : i ≠ j := fun e => by rw [e] at hi; omega
    simp [this]
  refine ⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩
  show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0
  rw [if_pos le_rfl]
  simpa using ha
end ReciprocityTheory.MultiplicativeHeights.SemiPt
