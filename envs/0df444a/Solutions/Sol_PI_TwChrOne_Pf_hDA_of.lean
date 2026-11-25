-- Prove2me | solution 1 for PI.TwChrOne.Pf.hDA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:15.948343+00:00
-- url     : https://prove2.me/submissions/bf789331-5c2a-41ff-b7db-c663149eab59

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_reduction_eq_zero
import Theorems.Thm_PI_TwChrOne_Pf_int_of_mem_stdAt
import Theorems.Thm_PI_TwChrOne_Pf_mem_stdAt_of
import Theorems.Thm_PI_TwChrOne_Pf_mem_parL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
private lemma intAt_inv_absNorm_mul_apply_of_mem_JQ {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
    (i : Fin (N + c)) (hi1 : kj ≤ i.1) (hi2 : i.1 < N) (j : Fin (N + c)) (hj : ¬(kj ≤ j.1 ∧ j.1 < N)) :
    IntAt P (((Ideal.absNorm P.asIdeal : ℕ) : E)⁻¹ * r (Loc.eN E (N + c) j.1) i) := by
  have hej : Loc.eN E (N + c) j.1 ∈ LocE.parL P (Ideal.absNorm P.asIdeal) kj N c := by
    rw [mem_parL]
    refine mem_stdAt_of P fun l => ?_
    by_cases hl : kj ≤ l.1 ∧ l.1 < N
    · have hlj : l.1 ≠ j.1 := fun h => hj (h ▸ hl)
      exact ⟨0, by simp [Loc.eN, hlj]⟩
    · refine ⟨if l.1 = j.1 then 1 else 0, ?_⟩
      simp only [Loc.eN, if_neg hl, zpow_zero, inv_one, one_mul]
      split_ifs <;> simp
  have h1 := (Subgroup.mem_inf.1 hr).2 _ |>.2 hej
  rw [mem_parL] at h1
  have h2 := int_of_mem_stdAt P h1 i
  simpa only [if_pos (And.intro hi1 hi2), zpow_one] using h2
private lemma redP_eq_zero_of_intAt_inv_absNorm_mul {a : E} (h : IntAt P (((Ideal.absNorm P.asIdeal : ℕ) : E)⁻¹ * a)) :
    redP P a = 0 := by
  obtain ⟨r', s, hs, hrs⟩ := h
  have hq : ((Ideal.absNorm P.asIdeal : ℕ) : E) ≠ 0 :=
    Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  refine reduction_eq_zero P (p := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)) (Ideal.absNorm_mem _) hs (r := r') ?_
  rw [map_natCast, ← hrs, mul_left_comm, ← mul_assoc ((Ideal.absNorm P.asIdeal : ℕ) : E), mul_inv_cancel₀ hq, one_mul]
variable {K : Type} [Field K]
end PI.TwChrOne.Pf
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0 :=
  fun i hi1 hi2 j hj => redP_eq_zero_of_intAt_inv_absNorm_mul P (intAt_inv_absNorm_mul_apply_of_mem_JQ P hr i hi1 hi2 j hj)
end PI.TwChrOne.Pf
