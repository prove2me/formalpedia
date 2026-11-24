-- Prove2me | solution 1 for RevRedSAT.lemma_B_8
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:20:06.700634+00:00
-- url     : https://prove2.me/submissions/e50e7865-50e4-4988-bf22-d0acb3e4024d

import Mathlib
import Definitions.Def_RevRedSAT_mu
import Definitions.Def_RevRedSAT_frequency

set_option autoImplicit false

namespace RevRedSATB8Aux

open RevRedSAT

lemma aval_eq (d j : ℕ) : Aval d j = 2 * d * (2 : ℝ) ^ j := by
  unfold Aval deltaOf
  rw [div_inv_eq_mul]

lemma aval_ge (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) : 4 * (d : ℝ) ≤ Aval d j ∧ 16 ≤ Aval d j := by
  rw [aval_eq]
  have h4 : (4 : ℝ) ≤ 2 ^ j := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor <;> nlinarith

lemma tp_mono (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {p q : ℕ} (hpq : p ≤ q) :
    tp d j p ≤ tp d j q := by
  unfold tp
  have hA := (aval_ge d j hd hj).2
  have hd' : (0 : ℝ) < 4 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  apply div_le_div_of_nonneg_right _ hd'.le
  exact pow_le_pow_right₀ (by linarith) (by omega)

lemma one_le_tp (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {p : ℕ} (hp : 1 ≤ p) : 1 ≤ tp d j p := by
  have h := tp_mono d j hd hj hp
  refine le_trans ?_ h
  unfold tp
  obtain ⟨h4, h16⟩ := aval_ge d j hd hj
  have hd' : (0 : ℝ) < 4 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [le_div_iff₀ hd', one_mul]
  have : Aval d j ≤ Aval d j ^ (4 * 1) := by
    rw [show 4 * 1 = 4 by rfl]
    nlinarith [pow_le_pow_right₀ (show (1 : ℝ) ≤ Aval d j by linarith) (show 1 ≤ 4 by norm_num)]
  linarith

end RevRedSATB8Aux

open RevRedSAT RevRedSATB8Aux in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ (j n : ℕ) (F : Finset (Finset (Fin n))), 2 ≤ j → (∀ S ∈ F, S.card ≤ d) →
      (∀ S ∈ F, S.Nonempty) → IsReduced F → IsSparse d j F → (frequency F : ℝ) ≤ Td d j) ∧
    (∃ C : ℝ, ∀ j : ℕ, 2 ≤ j → Td d j ≤ C * deltaOf j ^ (-((4 * d - 4 : ℕ) : ℤ))) ∧
    (∀ j : ℕ, 2 ≤ j → Td d j ≤ (2 * d / deltaOf j) ^ (4 * d)) := by
  have hTd_eq : ∀ j : ℕ, Td d j = 1 + ∑ i ∈ Finset.range (d - 1), tp d j (1 + i) := by
    intro j
    unfold Td
    rw [show Finset.Icc 1 (d - 1) = Finset.Ico 1 d by ext x; simp; omega,
      Finset.sum_Ico_eq_sum_range]
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨?_, ?_, ?_⟩
  · intro j n F hj hrank hne _hred hsp
    classical
    -- per-element bound
    have hel : ∀ u : Fin n, (((F.filter fun S => u ∈ S).card : ℕ) : ℝ) ≤ Td d j := by
      intro u
      set G := F.filter fun S => u ∈ S with hG
      have hmaps : (G : Set (Finset (Fin n))).MapsTo (fun S => S.card) (Finset.range (d + 1)) := by
        intro S hS
        have hS' := Finset.mem_coe.mp hS
        rw [hG, Finset.mem_filter] at hS'
        simp only [Finset.coe_range, Set.mem_Iio]
        have := hrank S hS'.1
        omega
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      push_cast
      set bnd : ℕ → ℝ := fun s => if s = 0 then 0 else if s = 1 then 1 else tp d j (s - 1)
        with hbnd
      have hterm : ∀ s ∈ Finset.range (d + 1),
          (((G.filter fun S => S.card = s).card : ℕ) : ℝ) ≤ bnd s := by
        intro s _
        set Gs := G.filter fun S => S.card = s with hGs
        have memGs : ∀ S ∈ Gs, S ∈ F ∧ u ∈ S ∧ S.card = s := by
          intro S hS
          rw [hGs, Finset.mem_filter, hG, Finset.mem_filter] at hS
          exact ⟨hS.1.1, hS.1.2, hS.2⟩
        by_cases hs0 : s = 0
        · have : Gs = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro S hS
            obtain ⟨h1, _, h3⟩ := memGs S hS
            have := (hne S h1).card_pos
            omega
          simp [this, hbnd, hs0]
        by_cases hs1 : s = 1
        · have hle : Gs.card ≤ 1 := by
            rw [Finset.card_le_one]
            intro S hS T hT
            obtain ⟨_, huS, hcS⟩ := memGs S hS
            obtain ⟨_, huT, hcT⟩ := memGs T hT
            rw [hs1] at hcS hcT
            obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcS
            obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hcT
            rw [Finset.mem_singleton] at huS huT
            rw [← huS, ← huT]
          simp only [hbnd, hs0, hs1, if_false, if_true]
          exact_mod_cast hle
        have hb : bnd s = tp d j (s - 1) := by simp [hbnd, hs0, hs1]
        rw [hb]
        by_cases hc : Gs.card ≤ 1
        · have : ((Gs.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
          linarith [one_le_tp d j hd hj (show 1 ≤ s - 1 by omega)]
        · push Not at hc
          obtain ⟨S, hS, T, hT, hST⟩ := Finset.one_lt_card.mp hc
          obtain ⟨hSF, huS, hcS⟩ := memGs S hS
          obtain ⟨hTF, huT, hcT⟩ := memGs T hT
          have hcoreS : core Gs ⊆ S := by
            unfold core; exact Finset.inf_le (f := id) hS
          have hcoreT : core Gs ⊆ T := by
            unfold core; exact Finset.inf_le (f := id) hT
          have hucore : u ∈ core Gs := by
            unfold core
            rw [Finset.mem_inf]
            intro V hV
            exact (memGs V hV).2.1
          have hcard_lt : (core Gs).card < s := by
            have hsub : core Gs ⊆ S ∩ T := Finset.subset_inter hcoreS hcoreT
            have hlt : (S ∩ T).card < S.card := by
              apply Finset.card_lt_card
              refine ⟨Finset.inter_subset_left, fun h => hST ?_⟩
              have hST' : S ⊆ T := fun x hx => (Finset.mem_inter.mp (h hx)).2
              exact Finset.eq_of_subset_of_card_le hST' (by omega)
            have := Finset.card_le_card hsub
            omega
          have hflower : IsFlower (layer F s) s Gs := by
            refine ⟨?_, ⟨S, hS⟩, ⟨u, hucore⟩, hcard_lt⟩
            intro V hV
            obtain ⟨hVF, _, hVc⟩ := memGs V hV
            simp only [layer, Finset.mem_filter]
            exact ⟨⟨hVF, hVc⟩, hVc⟩
          have hlt := hsp s Gs hflower
          have hmono : tp d j (s - (core Gs).card) ≤ tp d j (s - 1) := by
            apply tp_mono d j hd hj
            have : 1 ≤ (core Gs).card := Finset.card_pos.mpr ⟨u, hucore⟩
            omega
          linarith
      calc ∑ s ∈ Finset.range (d + 1), (((G.filter fun S => S.card = s).card : ℕ) : ℝ)
          ≤ ∑ s ∈ Finset.range (d + 1), bnd s := Finset.sum_le_sum hterm
        _ = Td d j := by
          rw [hTd_eq j, show d + 1 = (d - 1) + 1 + 1 by omega, Finset.sum_range_succ',
            Finset.sum_range_succ']
          simp only [hbnd]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
            add_eq_right, Nat.add_one_sub_one, if_true]
          rw [add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          try split_ifs
          all_goals first | omega | (congr 1; omega)
    rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with hU | hU
    · have : frequency F = 0 := by
        unfold frequency; rw [hU, Finset.sup_empty]; rfl
      rw [this, Nat.cast_zero, hTd_eq j]
      have : 0 ≤ ∑ i ∈ Finset.range (d - 1), tp d j (1 + i) :=
        Finset.sum_nonneg fun i _ => le_trans zero_le_one (one_le_tp d j hd hj (by omega))
      linarith
    · obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_sup _ hU (fun u => (F.filter fun S => u ∈ S).card)
      unfold frequency
      rw [hu]
      exact hel u
  · refine ⟨1 + ∑ i ∈ Finset.range (d - 1), (2 * (d : ℝ)) ^ (4 * (1 + i)) / (4 * d), ?_⟩
    intro j hj
    have hD : deltaOf j ^ (-((4 * d - 4 : ℕ) : ℤ)) = ((2 : ℝ) ^ j) ^ (4 * d - 4) := by
      unfold deltaOf
      rw [zpow_neg, zpow_natCast, inv_pow, inv_inv]
    rw [hD, hTd_eq j, add_mul, one_mul, Finset.sum_mul]
    have hD1 : (1 : ℝ) ≤ ((2 : ℝ) ^ j) ^ (4 * d - 4) :=
      one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hsum : ∑ i ∈ Finset.range (d - 1), tp d j (1 + i) ≤
        ∑ i ∈ Finset.range (d - 1),
          (2 * (d : ℝ)) ^ (4 * (1 + i)) / (4 * d) * ((2 : ℝ) ^ j) ^ (4 * d - 4) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      unfold tp
      rw [aval_eq, mul_pow, div_mul_eq_mul_div]
      have hd4 : (0 : ℝ) < 4 * d := by linarith
      apply div_le_div_of_nonneg_right _ hd4.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by omega)
    linarith
  · intro j hj
    have hAdef : (2 * (d : ℝ) / deltaOf j) = Aval d j := rfl
    rw [hAdef, hTd_eq j]
    obtain ⟨h4, h16⟩ := aval_ge d j hd hj
    set A := Aval d j with hA
    have hA1 : (1 : ℝ) ≤ A := by linarith
    have hd4 : (0 : ℝ) < 4 * d := by linarith
    have hsum : ∑ i ∈ Finset.range (d - 1), tp d j (1 + i) ≤
        ∑ _i ∈ Finset.range (d - 1), A ^ (4 * d - 4) / (4 * d) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      unfold tp
      rw [← hA]
      apply div_le_div_of_nonneg_right _ hd4.le
      exact pow_le_pow_right₀ hA1 (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hP : 0 ≤ A ^ (4 * d - 4) := by positivity
    have hcoef : ((d - 1 : ℕ) : ℝ) * (A ^ (4 * d - 4) / (4 * d)) ≤ A ^ (4 * d - 4) := by
      rw [mul_div_assoc', div_le_iff₀ hd4]
      have : ((d - 1 : ℕ) : ℝ) ≤ 4 * d := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      nlinarith
    have hpow : A ^ (4 * d) = A ^ (4 * d - 4) * A ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have hA4 : (2 : ℝ) ≤ A ^ 4 := by
      have := pow_le_pow_right₀ hA1 (show 1 ≤ 4 by norm_num)
      rw [pow_one] at this
      linarith
    have hP1 : 1 ≤ A ^ (4 * d - 4) := one_le_pow₀ hA1
    rw [hpow]
    nlinarith
