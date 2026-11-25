-- Prove2me | solution 1 for PI.Residue.exists_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:47.759636+00:00
-- url     : https://prove2.me/submissions/50fc54af-5296-4862-9625-0102057fcb12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Theorems.Thm_PI_Residue_one_lt_absNorm_of_mem
import Theorems.Thm_PI_Residue_exists_idx
import Theorems.Thm_PI_Residue_position_inj
import Theorems.Thm_PI_Residue_prod_position


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
theorem _root_.solution : ∃ n : {I : Ideal (𝓞 E) // I ≠ ⊥} → Fin (Module.finrank ℚ E) → ℕ,
    Function.Injective n ∧ ∀ I, ∏ i, n I i = absNorm I.1 := by
  classical
  obtain ⟨idx, hidx⟩ := exists_idx E
  have hmem : ∀ (I : Ideal (𝓞 E)), ∀ P ∈ normalizedFactors I, P ∈ primeSet E := by
    intro I P hP
    have hp := prime_of_normalized_factor P hP
    exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  refine ⟨fun I => intersection_update_fsHerm_neg_one (fun P => absNorm P) idx (normalizedFactors I.1), ?_, ?_⟩
  · intro I J hIJ
    have := position_inj (fun P : Ideal (𝓞 E) => absNorm P) idx (primeSet E)
      (fun P hP => one_lt_absNorm_of_mem hP) hidx (hmem I.1) (hmem J.1) hIJ
    apply Subtype.ext
    rw [← Ideal.prod_normalizedFactors_eq_self I.2, ← Ideal.prod_normalizedFactors_eq_self J.2,
      this]
  · intro I
    rw [prod_position, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self I.2]
end PI.Residue
