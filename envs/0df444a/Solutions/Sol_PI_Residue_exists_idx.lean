-- Prove2me | solution 1 for PI.Residue.exists_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:21.873246+00:00
-- url     : https://prove2.me/submissions/7be45da8-e161-4dc8-9862-a20e0716182c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Theorems.Thm_PI_Residue_exists_injOn_primesOver
import Theorems.Thm_PI_Residue_under_eq_of_not_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal
variable (E : Type*) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable (E)
namespace PI.Residue
theorem _root_.solution : ∃ idx : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
    ∀ P ∈ primeSet E, ∀ Q ∈ primeSet E, idx P = idx Q →
      ¬ Nat.Coprime (absNorm P) (absNorm Q) → P = Q := by
  classical
  have H : ∀ p : Ideal ℤ, ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
      p.IsMaximal → p ≠ ⊥ → Set.InjOn g (p.primesOver (𝓞 E)) := by
    intro p
    by_cases h : p.IsMaximal ∧ p ≠ ⊥
    · have := h.1
      obtain ⟨g, hg⟩ := exists_injOn_primesOver E p h.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨fun _ => ⟨0, Module.finrank_pos⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using H
  refine ⟨fun P => g (P.under ℤ) P, ?_⟩
  intro P hP Q hQ hidx hcop
  have key := under_eq_of_not_coprime hP hQ hcop
  have := hP.1
  have := hQ.1
  have hbot : Q.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hQ.2
  have hprime : (Q.under ℤ).IsPrime := inferInstance
  have hmax : (Q.under ℤ).IsMaximal := hprime.isMaximal hbot
  simp only [key] at hidx
  refine hg (Q.under ℤ) hmax hbot ⟨hP.1, ⟨key.symm⟩⟩ ⟨hQ.1, ⟨rfl⟩⟩ hidx
end PI.Residue
