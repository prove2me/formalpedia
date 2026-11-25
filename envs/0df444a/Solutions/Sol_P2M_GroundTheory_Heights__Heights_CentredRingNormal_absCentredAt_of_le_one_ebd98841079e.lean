-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CentredRingNormal_absCentredAt_of_le_one_ebd98841079e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:06.669527+00:00
-- url     : https://prove2.me/submissions/cf24be72-a3cc-45ee-95b0-1b5782144a8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SubringPrimeMaximal_proof_6f25c325f70e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
namespace GroundTheory.Heights₂.Heights.CentredRingNormal
theorem _root_.solution (O : Subalgebra ℤ L) [IsFractionRing O L] (m : Ideal O) [m.IsMaximal]
    (w : FinitePlace L)
    (hA : ∀ y ∈ Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors,
      w y ≤ 1)
    (x : L) (hx : 1 < w x) : AbsCentredAt O m fun t ↦ w t := by
  have hO : ∀ u : O, w u ≤ 1 := fun u ↦ hA _ (Subalgebra.algebraMap_mem _ u)
  let q : Ideal O :=
    { carrier := {u | w u < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        change w ((a : L) + b) < 1
        exact (FinitePlace.add_le w _ _).trans_lt (max_lt ha hb)
      smul_mem' := fun c a ha ↦ by
        change w ((c : L) * a) < 1
        rw [map_mul]
        exact (mul_le_of_le_one_left (apply_nonneg w _) (hO c)).trans_lt ha }
  have hmem : ∀ u : O, u ∈ q ↔ w u < 1 := fun _ ↦ Iff.rfl
  have hq_prime : q.IsPrime := by
    refine ⟨fun h ↦ ?_, fun {a b} hab ↦ ?_⟩
    · have h1 : (1 : O) ∈ q := h ▸ Submodule.mem_top
      rw [hmem] at h1
      simp at h1
    · by_contra hne
      rw [not_or, hmem, hmem, not_lt, not_lt] at hne
      rw [hmem] at hab
      change w ((a : L) * b) < 1 at hab
      rw [map_mul, le_antisymm (hO a) hne.1, le_antisymm (hO b) hne.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hq_ne : q ≠ ⊥ := by
    intro hq
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb1 : w (algebraMap O L b) = 1 := by
      refine le_antisymm (hO b) (not_lt.mp fun h ↦ nonZeroDivisors.ne_zero hb ?_)
      rw [← Ideal.mem_bot, ← hq]
      exact h
    rw [map_div₀, hb1, div_one] at hx
    exact absurd (hO a) (not_le.mpr hx)
  have hq_max : q.IsMaximal := SubringPrimeMaximal.proof L O q hq_prime hq_ne
  have hqm : q ≤ m := fun u hu ↦ by
    by_contra hum
    have hu0 : (u : L) ≠ 0 := fun h ↦ hum (by rw [show u = 0 from Subtype.ext h]; exact m.zero_mem)
    have hinv : w (u : L)⁻¹ ≤ 1 := hA _ ⟨1, u, hum, by rw [map_one, one_mul]; rfl⟩
    have hprod : w (u : L) * w (u : L)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hu' : w u < 1 := hu
    nlinarith [apply_nonneg w (u : L), apply_nonneg w (u : L)⁻¹]
  have hqe : q = m := hq_max.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hqm
  refine ⟨hO, fun u ↦ ?_⟩
  rw [← hqe]
  exact (hmem u).symm
end GroundTheory.Heights₂.Heights.CentredRingNormal
