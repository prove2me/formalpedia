-- Prove2me | solution 1 for PI.FGTFG.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:13.711879+00:00
-- url     : https://prove2.me/submissions/b64c0504-e80a-4016-a418-39f02c6862f4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf
import Theorems.Thm_PI_FGTFG_nzsd_sub
import Theorems.Thm_PI_FGTFG_peel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module
namespace PI.FGTFG
theorem _root_.solution (hS : SplitStep) (h1 : RankOneStep) (R : Type) [CommRing R] [IsDedekindDomain R] :
    ∀ n : ℕ, ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [NoZeroSMulDivisors R M], finrank R M = n →
      ∃ s : Finset M, s.card ≤ n + 1 ∧ Submodule.span R (s : Set M) = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ hM
    have : Subsingleton M := Module.finrank_zero_iff.mp hM
    exact ⟨∅, by simp, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M _ _ _ _ hM
    rcases Nat.lt_or_ge n 1 with hn | hn
    · obtain ⟨s, hs, hsp⟩ := h1 R M (by omega)
      exact ⟨s, by omega, hsp⟩
    · obtain ⟨φ, b, hb, hφ⟩ := hS R M (by omega)
      obtain ⟨hr, e, he⟩ := peel φ b hb hφ
      haveI := nzsd_sub (LinearMap.ker φ)
      obtain ⟨s, hs, hspan⟩ := ih (LinearMap.ker φ) (by omega)
      classical
      refine ⟨insert e (s.map (Function.Embedding.subtype _)), ?_, ?_⟩
      · calc _ ≤ (s.map (Function.Embedding.subtype _)).card + 1 := Finset.card_insert_le _ _
          _ ≤ n + 1 + 1 := by rw [Finset.card_map]; omega
      · have himg : Submodule.span R ((s.map (Function.Embedding.subtype _) : Finset M) : Set M)
            = LinearMap.ker φ := by
          rw [Finset.coe_map, Function.Embedding.coe_subtype]
          have := Submodule.span_image (R := R) (s := (s : Set (LinearMap.ker φ)))
            (LinearMap.ker φ).subtype
          rw [Submodule.coe_subtype] at this
          rw [this, hspan, Submodule.map_top, Submodule.range_subtype]
        rw [Finset.coe_insert, Submodule.span_insert, himg, sup_comm, he]
end PI.FGTFG
