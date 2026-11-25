-- Prove2me | solution 1 for PI.VolStabW.FFHS.frob_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:35.750927+00:00
-- url     : https://prove2.me/submissions/fece2221-15b1-4431-a4f1-7173b627fcaf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabW.FFHS
theorem _root_.solution (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  obtain ⟨⟨n, hn'⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).2 σ
  simp only at hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · exact absurd (by rw [← hn, pow_zero]; rfl) hne
  · intro x
    rw [← hn, pow_one]
    rfl
end PI.VolStabW.FFHS
