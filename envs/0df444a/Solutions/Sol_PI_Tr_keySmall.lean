-- Prove2me | solution 1 for PI.Tr.keySmall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:40.052835+00:00
-- url     : https://prove2.me/submissions/9b9ae7b2-a39b-4f80-8a21-b8ad0f167816

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_KeySmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
namespace PI.Tr
private theorem exists_generator_of_finrank_eq_one_zLattice {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h1 : finrank ℝ E = 1) :
    ∃ a ∈ Λ, a ≠ 0 ∧ ∀ x ∈ Λ, ∃ k : ℤ, x = (k : ℝ) • a := by
  have hrk : finrank ℤ Λ = 1 := (ZLattice.rank ℝ Λ).trans h1
  let b := Module.finBasisOfFinrankEq ℤ Λ hrk
  refine ⟨(b 0 : E), (b 0).2, fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩
  intro x hx
  refine ⟨b.repr ⟨x, hx⟩ 0, ?_⟩
  have h2 : ((b.repr ⟨x, hx⟩ 0 • b 0 : Λ) : E) = x := by
    have hs := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at hs
    rw [hs]
  rw [Int.cast_smul_eq_zsmul]
  exact h2.symm.trans (Submodule.coe_smul _ _)
end PI.Tr
end

set_option autoImplicit false
open Module
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution : KeySmall := by
  intro E _ _ _ Λ _ _ lam u hdim hlam hdual
  have hdim' : finrank ℝ E ≤ 1 := hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim' with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    refine ⟨0, Λ.zero_mem, ?_⟩
    rw [Subsingleton.elim u 0, h0]
    simp
  · obtain ⟨a, haΛ, ha0, hmul⟩ := exists_generator_of_finrank_eq_one_zLattice Λ h1
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).mp h1 u
      exact ⟨c, hc.symm⟩
    have hα : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    rw [h1, Nat.cast_one]
    by_cases hc : lam * ‖a‖ ≤ 1
    · refine ⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        calc |t - ((round t : ℤ) : ℝ)| * ‖a‖ * lam ≤ (1 / 2) * ‖a‖ * lam :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg a)) hlam.le
          _ = (1 / 2) * (lam * ‖a‖) := by ring
          _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hc (by norm_num)
          _ = 1 / 2 := by ring
    · push Not at hc
      have hα2 : ‖a‖ ^ 2 ≠ 0 := by positivity
      have key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s := by
        intro s
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
          inv_mul_cancel₀ hα2, mul_one]
      have hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam := by
        rw [norm_smul, norm_inv, norm_pow, norm_norm]
        have e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1 := by
          rw [mul_assoc, ← sq, inv_mul_cancel₀ hα2]
        have hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖ := by
          rw [e]
          exact hc
        exact lt_of_mul_lt_mul_right hlt hα.le
      obtain ⟨m, hm⟩ := hdual ((‖a‖ ^ 2)⁻¹ • a)
        (by
          intro x hx
          obtain ⟨k, rfl⟩ := hmul x hx
          exact ⟨k, key _⟩) hnorm
      rw [key] at hm
      refine ⟨(m : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [hm, sub_self, norm_zero, zero_mul]
        norm_num
end PI.Tr
