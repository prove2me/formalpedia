-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_exists_norm_untilt_eq_norm_of_norm_le_one_ecbe03a01da8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:57.263775+00:00
-- url     : https://prove2.me/submissions/8d8e131e-f813-42f3-8d8e-97dcba24ae09

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GroundTheory.Variant₂.N1
open GroundTheory.PAdicHodge
section
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
private lemma mem_integers_iff (x : K) : x ∈ (normInteger K) ↔ ‖x‖ ≤ 1 := by
  change NormedField.valuation x ≤ 1 ↔ _
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
private lemma norm_eq_of_norm_sub_lt {u z : K} (h : ‖u - z‖ < ‖z‖) : ‖u‖ = ‖z‖ := by
  have h1 : ‖u‖ ≤ max ‖u - z‖ ‖z‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (u - z) z
  have h2 : ‖z‖ ≤ max ‖z - u‖ ‖u‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (z - u) u
  rw [norm_sub_rev] at h2
  apply le_antisymm
  · exact h1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.mp h2 with h3 | h3
    · exact absurd h3 (not_le.mpr h)
    · exact h3
private lemma norm_le_of_mem_span {x : (normInteger K)} {p : ℕ}
    (hx : x ∈ Ideal.span {((p : (normInteger K)))}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hc : ‖(c : K)‖ ≤ 1 := (mem_integers_iff (c : K)).mp c.2
  simp only [Subring.coe_mul, Subring.coe_natCast, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : (normInteger K))] [IsAdicComplete (Ideal.span {(p : (normInteger K))}) (normInteger K)]
private lemma exists_untilt_norm_of_lt
    (hsurj : Function.Surjective fun x : ModP (normInteger K) p => x ^ p)
    {x : K} (hpx : ‖(p : K)‖ < ‖x‖) (hx1 : ‖x‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : (normInteger K)) : K)‖ = ‖x‖ := by
  let x' : (normInteger K) := ⟨x, (mem_integers_iff x).mpr hx1⟩
  let s : ℕ → ModP (normInteger K) p := fun n => Nat.rec (Ideal.Quotient.mk _ x')
    (fun _ t => Classical.choose (hsurj t)) n
  have hs : ∀ n, s (n + 1) ^ p = s n := fun n => Classical.choose_spec (hsurj (s n))
  let a : PreTilt (normInteger K) p := ⟨s, hs⟩
  refine ⟨a, ?_⟩
  have h0 : Ideal.Quotient.mk _ (PreTilt.untilt a) = Ideal.Quotient.mk (Ideal.span {(p : (normInteger K))}) x' := by
    rw [PreTilt.mk_untilt_eq_coeff_zero]
    rfl
  have hdiff : ‖((PreTilt.untilt a : (normInteger K)) : K) - x‖ ≤ ‖(p : K)‖ := by
    have hmem := Ideal.Quotient.eq.mp h0
    simpa [x'] using norm_le_of_mem_span hmem
  exact norm_eq_of_norm_sub_lt (lt_of_le_of_lt hdiff hpx)
private lemma exists_untilt_norm
    (hsurj : Function.Surjective fun x : ModP (normInteger K) p => x ^ p)
    {t : K} (hpt : ‖(p : K)‖ < ‖t‖) (ht1 : ‖t‖ < 1)
    {y : K} (hy : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : (normInteger K)) : K)‖ = ‖y‖ := by
  obtain ⟨at', hat⟩ := exists_untilt_norm_of_lt hsurj hpt ht1.le
  have ht0 : 0 < ‖t‖ := lt_of_le_of_lt (norm_nonneg _) hpt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hy) ht1

  induction n generalizing y with
  | zero =>
    exact absurd hy1 (not_le.mpr (by simpa using hn))
  | succ n ih =>
    by_cases hyt : ‖t‖ < ‖y‖
    · exact exists_untilt_norm_of_lt hsurj (hpt.trans hyt) hy1
    · rw [not_lt] at hyt
      have htne : t ≠ 0 := norm_pos_iff.mp ht0
      have hv : ‖y / t‖ = ‖y‖ / ‖t‖ := norm_div y t
      obtain ⟨b, hb⟩ := ih (y := y / t) (div_ne_zero hy htne)
        (by rw [hv]; exact (div_le_one ht0).mpr hyt)
        (by rw [hv, lt_div_iff₀ ht0, ← pow_succ]; exact hn)
      refine ⟨at' * b, ?_⟩
      rw [map_mul, Subring.coe_mul, norm_mul, hat, hb, hv, mul_div_cancel₀ _ ht0.ne']
end
end GroundTheory.Variant₂.N1
end

set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open GroundTheory.PAdicHodge
namespace GroundTheory.Variant₂.N1
theorem _root_.solution {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] {p : ℕ} [Fact (Nat.Prime p)] [IsPerfectoidField K p] {y : K}
    (hy : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : PreTilt (normInteger K) p, ‖((PreTilt.untilt a : normInteger K) : K)‖ = ‖y‖ := by
  obtain ⟨t, hpt, ht1⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) p ‖(p : K)‖
    IsPerfectoidField.norm_natCast_lt_one
  exact exists_untilt_norm IsPerfectoidField.surjective_pow hpt ht1 hy hy1
end GroundTheory.Variant₂.N1
