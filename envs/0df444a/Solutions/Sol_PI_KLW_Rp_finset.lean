-- Prove2me | solution 1 for PI.KLW.Rp_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:10.831823+00:00
-- url     : https://prove2.me/submissions/87161253-dea5-4b95-bbb5-923caf53cf84

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW
theorem _root_.solution {α : Type} (T : Finset α) (f : α → K) (h : ∀ z ∈ T, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z ∈ T, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | insert a T ha ih =>
    obtain ⟨s, hs, hsT⟩ := ih fun z hz => h z (Finset.mem_insert_of_mem hz)
    obtain ⟨t, ht, hta⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have e : ((s * t : ℕ) : K) * f z = (s : K) * ((t : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ s) hta
    · have e : ((s * t : ℕ) : K) * f z = (t : K) * ((s : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ t) (hsT z hz)
end PI.KLW
