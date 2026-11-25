-- Prove2me | solution 1 for PI.Residue.exists_injOn_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:25.175939+00:00
-- url     : https://prove2.me/submissions/2ae078c5-5949-4ec3-b1b1-049d1e6b3f71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime

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
set_option linter.deprecated false
namespace PI.Residue
theorem _root_.solution (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E), Set.InjOn g (p.primesOver (𝓞 E)) := by
  have hcard := Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hp
  have : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hfin : (p.primesOver (𝓞 E)).Finite := by
    rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E)]
    exact Finset.finite_toSet _
  obtain ⟨f, -, hf⟩ := hfin.exists_injOn_of_encard_le
    (t := (Set.univ : Set (Fin (Module.finrank ℚ E)))) (by
      rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E), Set.encard_coe_eq_coe_finsetCard,
        Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      exact_mod_cast hcard)
  exact ⟨f, hf⟩
end PI.Residue
