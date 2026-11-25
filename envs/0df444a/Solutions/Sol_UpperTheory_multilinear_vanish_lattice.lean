-- Prove2me | solution 1 for UpperTheory.multilinear_vanish_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:47.985953+00:00
-- url     : https://prove2.me/submissions/d9e8f2cf-58de-4da1-8a8f-e038265631c3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultilinearVanishLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {ι : Type} [Finite ι] [DecidableEq ι] {M : ι → Type} {N : Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
        [AddCommGroup N] [Module ℂ N] (T : MultilinearMap ℂ M N) (L G : ∀ i, Set (M i)),
        (∀ v : ∀ i, M i, (∀ i, v i ∈ L i) → T v = 0) →
        (∀ i, ∀ w ∈ G i, ∃ w0 ∈ L i, ∀ v : ∀ i, M i, T (Function.update v i w0) = 0 → T (Function.update v i w) = 0) →
        ∀ v : ∀ i, M i, (∀ i, v i ∈ Submodule.span ℂ (G i)) → T v = 0 := by
  intro ι _ _ M N _ _ _ _ T L G hL hG
  have key : ∀ s : Finset ι, ∀ v : ∀ i, M i, (∀ i ∈ s, v i ∈ Submodule.span ℂ (G i)) →
      (∀ i, i ∉ s → v i ∈ L i) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h => hL v fun i => h i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro v hs hn
      have hker : Submodule.span ℂ (G a) ≤ LinearMap.ker (T.toLinearMap v a) := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨w0, hw0, h⟩ := hG a w hw
        have h0 : T (Function.update v a w0) = 0 := by
          apply ih
          · intro i hi
            have hia : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne hia]
            exact hs i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases hia : i = a
            · subst hia
              rw [Function.update_self]
              exact hw0
            · rw [Function.update_of_ne hia]
              exact hn i (by simp [hia, hi])
        exact h v h0
      have hv : T (Function.update v a (v a)) = 0 := hker (hs a (Finset.mem_insert_self a s))
      rwa [Function.update_eq_self] at hv
  intro v hv
  haveI := Fintype.ofFinite ι
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)
end UpperTheory
