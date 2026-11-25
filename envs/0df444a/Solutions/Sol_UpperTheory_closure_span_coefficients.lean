-- Prove2me | solution 1 for UpperTheory.closure_span_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:24.438668+00:00
-- url     : https://prove2.me/submissions/125b3275-3419-4e36-a680-65e1311d89ec

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureSpanCoefficients

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
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by
  intro R M L _ _ _ _ O f m x hx z
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, rfl⟩ := hz
      have hl : l ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hl
      refine ⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    | zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, fun i => O.add_mem (ha i) (hb i), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨-a, fun i => O.neg_mem (ha i), by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩
end UpperTheory
