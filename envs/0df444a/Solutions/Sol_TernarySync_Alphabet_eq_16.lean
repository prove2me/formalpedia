-- Prove2me | solution 1 for TernarySync.Alphabet.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:51.587792+00:00
-- url     : https://prove2.me/submissions/0fbe7ff2-b778-43ba-b3c8-08263c7fb810

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

section
set_option autoImplicit false

namespace TernarySync.Dev.Eq16
open TernarySync.Alphabet

/-- `q = e^{-1/80}`. -/
noncomputable def q : ℝ := Real.exp (-(1 / 80))

theorem q_pos : 0 < q := Real.exp_pos _

theorem q_lt_one : q < 1 := by
  unfold q; rw [Real.exp_lt_one_iff]; norm_num

theorem exp_term (k : ℕ) : Real.exp (-((k : ℝ) + 1000) / 80) = q ^ 1000 * q ^ k := by
  unfold q
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; push_cast; ring

theorem q_mul_exp : q * Real.exp (1 / 80) = 1 := by
  unfold q; rw [← Real.exp_add]; simp

theorem exp_small : (1 : ℝ) + 1 / 80 + (1 / 80) ^ 2 / 2 ≤ Real.exp (1 / 80) :=
  Real.quadratic_le_exp_of_nonneg (by norm_num)

theorem inv_one_sub_q_le : (1 - q)⁻¹ ≤ 80.51 := by
  have h1 := q_mul_exp
  have h2 := exp_small
  have hq := q_pos
  have h3 : q * (1 + 1 / 80 + (1 / 80) ^ 2 / 2) ≤ 1 := by
    calc _ ≤ q * Real.exp (1 / 80) := by gcongr
      _ = 1 := h1
  have h4 : 0 < 1 - q := by linarith [q_lt_one]
  rw [inv_le_comm₀ h4 (by norm_num)]
  norm_num at h3 ⊢
  linarith

theorem q_pow_le : q ^ 1000 ≤ 3.8e-6 := by
  have h1 : q ^ 1000 = (Real.exp (25 / 2))⁻¹ := by
    unfold q
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; norm_num
  have h2 : Real.exp (25 / 2) = Real.exp 1 ^ 12 * Real.exp (1 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num
  have h3 : (2.7182818283 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12
  have h4 : (1 : ℝ) + 1 / 2 + (1 / 2) ^ 2 / 2 ≤ Real.exp (1 / 2) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h5 : (264000 : ℝ) ≤ Real.exp (25 / 2) := by
    rw [h2]
    have : (2.7182818283 : ℝ) ^ 12 * (1 + 1 / 2 + (1 / 2) ^ 2 / 2) ≤
        Real.exp 1 ^ 12 * Real.exp (1 / 2) := by gcongr
    refine le_trans ?_ this
    norm_num
  rw [h1, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num
  linarith

/-- the summand of the series in the statement, as a function of `k = r'`. -/
noncomputable def g (ℓ : ℕ) (k : ℕ) : ℝ :=
  ((ℓ : ℝ) + ((k : ℝ) + 1000)) * Real.exp (-((k : ℝ) + 1000) / 80)

theorem g_eq (ℓ k : ℕ) :
    g ℓ k = q ^ 1000 * (((ℓ : ℝ) + 1000) * q ^ k + (k : ℝ) * q ^ k) := by
  unfold g; rw [exp_term]; ring

theorem summable_g (ℓ : ℕ) : Summable (g ℓ) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos q_pos]; exact q_lt_one
  have h1 : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one q_pos.le q_lt_one
  have h2 : Summable fun k : ℕ => (k : ℝ) * q ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have := ((h1.mul_left ((ℓ : ℝ) + 1000)).add h2).mul_left (q ^ 1000)
  exact this.congr (fun k => (g_eq ℓ k).symm)

theorem tsum_g (ℓ : ℕ) :
    ∑' k, g ℓ k = q ^ 1000 * (((ℓ : ℝ) + 1000) * (1 - q)⁻¹ + q / (1 - q) ^ 2) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos q_pos]; exact q_lt_one
  have h1 : Summable fun k : ℕ => q ^ k := summable_geometric_of_lt_one q_pos.le q_lt_one
  have h2 : Summable fun k : ℕ => (k : ℝ) * q ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  simp_rw [g_eq]
  rw [tsum_mul_left, (h1.mul_left _).tsum_add h2, tsum_mul_left,
    tsum_geometric_of_lt_one q_pos.le q_lt_one, tsum_coe_mul_geometric_of_norm_lt_one hn]

theorem three_tsum_lt (ℓ : ℕ) (hℓ : 1000 < ℓ) : 3 * ∑' k, g ℓ k < (ℓ : ℝ) / 490 := by
  rw [tsum_g]
  have hℓ' : (1000 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hq := q_pos
  have h4 : 0 < 1 - q := by linarith [q_lt_one]
  have hS := inv_one_sub_q_le
  have hS0 : 0 < (1 - q)⁻¹ := inv_pos.2 h4
  have hS1 : q / (1 - q) ^ 2 ≤ ((1 - q)⁻¹) ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
    have : (1 - q) ^ 2 ≠ 0 := by positivity
    have h5 : 0 < ((1 - q) ^ 2)⁻¹ := by positivity
    nlinarith [q_lt_one]
  have hS1' : q / (1 - q) ^ 2 ≤ 6482 := by
    refine hS1.trans ?_
    nlinarith
  have hqp := q_pow_le
  have hqp0 : 0 ≤ q ^ 1000 := by positivity
  have hin : ((ℓ : ℝ) + 1000) * (1 - q)⁻¹ + q / (1 - q) ^ 2 ≤ ((ℓ : ℝ) + 1000) * 80.51 + 6482 := by
    have : ((ℓ : ℝ) + 1000) * (1 - q)⁻¹ ≤ ((ℓ : ℝ) + 1000) * 80.51 := by gcongr
    linarith
  have hin' : q ^ 1000 * (((ℓ : ℝ) + 1000) * (1 - q)⁻¹ + q / (1 - q) ^ 2) ≤
      3.8e-6 * (((ℓ : ℝ) + 1000) * 80.51 + 6482) := by
    calc _ ≤ q ^ 1000 * (((ℓ : ℝ) + 1000) * 80.51 + 6482) := by gcongr
      _ ≤ _ := by gcongr
  nlinarith


theorem fiber_card (N t ℓ r : ℕ) (hr : 1000 < r) (hℓ : 1000 < ℓ) :
    ((neighbours N t ℓ).filter fun p => p.2 = r).card ≤ 3 * (ℓ + r) := by
  have hsub : ((neighbours N t ℓ).filter fun p => p.2 = r).card ≤
      (Finset.Ico (t - 2 * r - 17) (t + 2 * ℓ + 17)).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      have hpr : p.2 = r := hp'.2
      have hnb := (Finset.mem_filter.1 hp'.1).2.2
      obtain ⟨i, hi⟩ := hnb
      simp only [eventVars, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hi
      simp only [Finset.coe_Ico, Set.mem_Ico]
      omega
    · intro p hp p' hp' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hp'
      exact Prod.ext h (hp.2.trans hp'.2.symm)
  refine hsub.trans ?_
  rw [Nat.card_Ico]
  omega

theorem sum_le (N t ℓ : ℕ) (hℓ : 1000 < ℓ) :
    ∑ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80) ≤ 3 * ∑' k, g ℓ k := by
  classical
  set S := neighbours N t ℓ with hS
  have hr : ∀ p ∈ S, 1000 < p.2 := by
    intro p hp
    simp only [hS, neighbours, availEvents, Finset.mem_filter] at hp
    exact hp.1.2.1
  have h1 : ∑ p ∈ S, Real.exp (-(p.2 : ℝ) / 80) =
      ∑ r ∈ S.image Prod.snd, ((S.filter fun p => p.2 = r).card : ℝ) * Real.exp (-(r : ℝ) / 80) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := S.image Prod.snd)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun r hr' => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.exp (-(r : ℝ) / 80))
      (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have h2 : ∀ r ∈ S.image Prod.snd,
      ((S.filter fun p => p.2 = r).card : ℝ) * Real.exp (-(r : ℝ) / 80) ≤
        3 * g ℓ (r - 1000) := by
    intro r hr'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr'
    have h1000 := hr p hp
    have hc := fiber_card N t ℓ p.2 h1000 hℓ
    have hc' : ((S.filter fun x => x.2 = p.2).card : ℝ) ≤ 3 * ((ℓ : ℝ) + p.2) := by
      exact_mod_cast hc
    have : g ℓ (p.2 - 1000) = ((ℓ : ℝ) + p.2) * Real.exp (-(p.2 : ℝ) / 80) := by
      unfold g
      have : (((p.2 - 1000 : ℕ) : ℝ) + 1000) = p.2 := by
        rw [Nat.cast_sub h1000.le]; push_cast; ring
      rw [this]
    rw [this]
    have := Real.exp_pos (-(p.2 : ℝ) / 80)
    nlinarith
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  have hinj : Set.InjOn (fun r : ℕ => r - 1000) (S.image Prod.snd : Set ℕ) := by
    intro a ha b hb h
    have ha' := hr _ (Finset.mem_image.1 ha).choose_spec.1
    have hb' := hr _ (Finset.mem_image.1 hb).choose_spec.1
    have ha2 : 1000 < a := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha; exact hr p hp
    have hb2 : 1000 < b := by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb; exact hr p hp
    simp only at h
    omega
  have h3 : ∑ r ∈ S.image Prod.snd, g ℓ (r - 1000) =
      ∑ k ∈ (S.image Prod.snd).image (fun r => r - 1000), g ℓ k :=
    (Finset.sum_image hinj).symm
  rw [h3]
  gcongr
  exact (summable_g ℓ).sum_le_tsum _ (fun k _ => by
    unfold g; have := Real.exp_pos (-((k : ℝ) + 1000) / 80); positivity)

end TernarySync.Dev.Eq16

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq16 in
theorem chk_eq_16 (N t ℓ : ℕ) (hE : (t, ℓ) ∈ availEvents N) :
    ∑ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80) ≤
        3 * ∑' r : ℕ, ((ℓ : ℝ) + ((r : ℝ) + 1000)) * Real.exp (-((r : ℝ) + 1000) / 80) ∧
      3 * ∑' r : ℕ, ((ℓ : ℝ) + ((r : ℝ) + 1000)) * Real.exp (-((r : ℝ) + 1000) / 80) <
        (ℓ : ℝ) / 490 := by
  have hℓ : 1000 < ℓ := by
    simp only [availEvents, Finset.mem_filter] at hE
    exact hE.2.1
  exact ⟨sum_le N t ℓ hℓ, three_tsum_lt ℓ hℓ⟩
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_16 := @TernarySync.Alphabet.chk_eq_16
