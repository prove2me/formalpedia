-- Prove2me | solution 1 for PI.SqPairLocal.good_pert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:55.742607+00:00
-- url     : https://prove2.me/submissions/00f13a5f-3320-4dd6-971e-e0c619027a84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_small_pert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} (h' : IsSDG E N L') (h'' : IsSDG E N L'')
    {e₀ D : Matrix (Fin N) (Fin N) E} {ρ : 𝓞 E} (hg : Good Q c L' L'' e₀)
    (h₀' : Pres L' e₀) (h₀'' : Pres L'' e₀) (hD' : Pres L' D) (hD'' : Pres L'' D)
    (hρ : Dv Q c ρ) (hρc : Dv Q c (cj E ρ)) : Good Q c L' L'' (e₀ + (ρ : E) • D) := by
  obtain ⟨a, b, c2, d⟩ := hg
  obtain ⟨x1, x2⟩ := small_pert h' h₀' hD' hρ hρc a c2
  obtain ⟨y1, y2⟩ := small_pert h'' h₀'' hD'' hρ hρc b d
  first
    | exact ⟨x1, y1, x2, y2⟩
    | (unfold Good; exact ⟨x1, y1, x2, y2⟩)
end PI.SqPairLocal
