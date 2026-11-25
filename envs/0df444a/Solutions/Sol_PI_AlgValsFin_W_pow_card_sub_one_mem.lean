-- Prove2me | solution 1 for PI.AlgValsFin.W.pow_card_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:22.659421+00:00
-- url     : https://prove2.me/submissions/024ceea7-ef31-4e68-a5ef-5c5e48cf2a17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace PI.AlgValsFin.W
theorem _root_.solution (n : ℕ) (b : 𝓞 L) (hb : b ∉ v.asIdeal) :
    b ^ Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) - 1 ∈ v.asIdeal ^ n := by
  obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hb
  have h1 : (y * ∑ k ∈ Finset.range n, i ^ k) * b = 1 - i ^ n := by
    have hyb : y * b = 1 - i := by linear_combination hyi
    calc (y * ∑ k ∈ Finset.range n, i ^ k) * b = (y * b) * ∑ k ∈ Finset.range n, i ^ k := by ring
      _ = (1 - i) * ∑ k ∈ Finset.range n, i ^ k := by rw [hyb]
      _ = 1 - i ^ n := mul_neg_geom_sum i n
  have hcb : Ideal.Quotient.mk (v.asIdeal ^ n) (y * ∑ k ∈ Finset.range n, i ^ k) *
      Ideal.Quotient.mk (v.asIdeal ^ n) b = 1 := by
    rw [← map_mul, h1, map_sub, map_one,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.pow_mem_pow hi n), sub_zero]
  let u : (𝓞 L ⧸ v.asIdeal ^ n)ˣ := ⟨Ideal.Quotient.mk _ b, Ideal.Quotient.mk _ (y * ∑ k ∈ Finset.range n, i ^ k),
    by rw [mul_comm]; exact hcb, hcb⟩
  have hu : u ^ Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) = 1 := pow_card_eq_one'
  have h2 := congrArg Units.val hu
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one]
  exact sub_eq_zero.mpr h2
end PI.AlgValsFin.W
