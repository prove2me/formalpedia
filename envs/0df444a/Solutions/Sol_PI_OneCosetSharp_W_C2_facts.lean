-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:32.214946+00:00
-- url     : https://prove2.me/submissions/a9cfac89-c2f9-4099-bd4e-5e7325b43250

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) :
    k₀ ≤ n' ∧ 1 ≤ c ∧ k₀ + c < k₀ + m - 1 ∧ k₀ + m - 1 ≤ n' + (c + 1) ∧ n' + (c + 1) ≤ n + c ∧
      n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = n' + (c + 1) + t := by
  obtain ⟨h1, -, h4, hj1, hjm, hc, he1, he2⟩ := h
  have hjt : j * t = (j - 1) * t + t := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [add_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, he1, ?_⟩ <;> omega
end PI.OneCosetSharp.W.C2
