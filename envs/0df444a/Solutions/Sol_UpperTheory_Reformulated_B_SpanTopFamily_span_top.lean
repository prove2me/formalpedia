-- Prove2me | solution 1 for UpperTheory.Reformulated.B.SpanTopFamily.span_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:12.059773+00:00
-- url     : https://prove2.me/submissions/c1972559-481b-49c1-934a-65a8f6b8e552

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanTopFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.SpanTopFamily
theorem _root_.solution :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h
end UpperTheory.Reformulated.B.SpanTopFamily
