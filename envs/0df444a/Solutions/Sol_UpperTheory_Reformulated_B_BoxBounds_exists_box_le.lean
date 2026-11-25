-- Prove2me | solution 1 for UpperTheory.Reformulated.B.BoxBounds.exists_box_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:47.171638+00:00
-- url     : https://prove2.me/submissions/a8ef9510-63d2-4f17-8342-a6c4f53867ea

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoxBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.BoxBounds
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by
  intro K _ _ i L hL
  classical
  have h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K),
      (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L := by
    intro j
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K))
      (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using h
  refine ⟨∏ j, (t j : NumberField.RingOfIntegers K),
    Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine L.sum_mem fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))
  obtain ⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hj : (Pi.single j (x j) : Fin i → K)
      = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) := by
    rw [← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    ring
  rw [hj]
  exact L.smul_mem _ (ht j)
end UpperTheory.Reformulated.B.BoxBounds
