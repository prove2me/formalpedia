-- Prove2me | solution 1 for PI.SqPairLocal.powLoc_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:12.524074+00:00
-- url     : https://prove2.me/submissions/1843f1ab-5595-4f97-8f43-19d85efc655d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj

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
namespace PI.SqPairLocal
theorem _root_.solution (hP : PowLoc) (S : Finset (Ideal (𝓞 E))) (hS : ∀ P ∈ S, P.IsMaximal)
    {c : 𝓞 E} (hc : c ≠ 0) : ∃ K : ℕ, ∀ P ∈ S, ∀ x ∈ P ^ K, Dv P c x := by
  classical
  have h1 : ∀ P ∈ S, ∃ K : ℕ, ∀ x ∈ P ^ K, Dv P c x := fun P hPS => hP E P (hS P hPS) c hc
  choose! Kf hKf using h1
  exact ⟨S.sup Kf, fun P hPS x hx =>
    hKf P hPS x (Ideal.pow_le_pow_right (Finset.le_sup hPS) hx)⟩
end PI.SqPairLocal
