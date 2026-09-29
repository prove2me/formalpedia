-- Prove2me | solution 1 for Tuple.succAbove_sort_comp_succAbove_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5fcbbcc2-719a-5772-8172-a1c3268b27a2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Tuple_succAbove_sort_comp_succAbove_eq

set_option autoImplicit false

theorem solution
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove k) := by
  classical
  set s : Equiv.Perm (Fin (n + 1)) := Tuple.sort u with hs
  set p : Fin (n + 1) := s.symm i with hp
  have hsp : s p = i := s.apply_symm_apply i

  let e : {x : Fin (n + 1) // x ≠ p} ≃ {x : Fin (n + 1) // x ≠ i} :=
    s.subtypeEquiv (fun x => by rw [← hsp]; exact s.injective.ne_iff.symm)
  let τ : Equiv.Perm (Fin n) := ((finSuccAboveEquiv p).trans e).trans (finSuccAboveEquiv i).symm
  have hτ : ∀ k : Fin n, i.succAbove (τ k) = s (p.succAbove k) := by
    intro k
    have h1 : finSuccAboveEquiv i (τ k) = e (finSuccAboveEquiv p k) :=
      (finSuccAboveEquiv i).apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    rw [finSuccAboveEquiv_apply] at h2
    simpa [e, Equiv.subtypeEquiv, finSuccAboveEquiv_apply] using h2
  have key : τ = Tuple.sort (u ∘ i.succAbove) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨?_, ?_⟩
    · intro a b hab
      show u (i.succAbove (τ a)) ≤ u (i.succAbove (τ b))
      rw [hτ, hτ]
      exact Tuple.monotone_sort u ((Fin.strictMono_succAbove p).monotone hab)
    · intro a b hab h
      exfalso
      have h' : i.succAbove (τ a) = i.succAbove (τ b) := hu h
      rw [hτ, hτ, s.apply_eq_iff_eq] at h'
      exact absurd (Fin.succAbove_right_injective h') hab.ne
  rw [← key, hτ]

end S_Tuple_succAbove_sort_comp_succAbove_eq
end P2MW
export P2MW.S_Tuple_succAbove_sort_comp_succAbove_eq (solution)
