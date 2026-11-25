-- Prove2me | solution 1 for PI.OmVf.quad_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:32.22384+00:00
-- url     : https://prove2.me/submissions/c1a03744-352c-455a-8f4a-57d0c32f7edf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_QuadRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.OmVf
namespace PI.OmVf
theorem _root_.solution {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu
end PI.OmVf
