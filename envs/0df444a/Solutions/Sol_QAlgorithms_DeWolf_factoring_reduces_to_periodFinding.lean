-- Prove2me | solution 1 for QAlgorithms.DeWolf.factoring_reduces_to_periodFinding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:54:19.594469+00:00
-- url     : https://prove2.me/submissions/bbba13f6-8d5b-4d28-b511-f084bbb1af4c

import Definitions.Def_QAlgorithms_Defs_Fourier
import Theorems.Thm_ShorAlgorithms_Reduction_factor_prob_ge
import Theorems.Thm_ShorWiki_gcd_pow_half_nontrivial

open QAlgorithms

private theorem period_of_coprime (N x : ℕ) (hN : 1 < N) (hc : Nat.Coprime x N) :
    0 < orderOf (x : ZMod N) ∧ orderOf (x : ZMod N) ≤ N ∧
      HasPeriod (fun a => x ^ a % N) (orderOf (x : ZMod N)) := by
  letI : NeZero N := ⟨by omega⟩
  have hu : IsUnit (x : ZMod N) := (ZMod.isUnit_iff_coprime x N).2 hc
  have hf := hu.isOfFinOrder
  refine ⟨hf.orderOf_pos, ?_, ?_⟩
  · exact (orderOf_le_card (x := (x : ZMod N))).trans (by simp)
  · intro a b
    rw [← ZMod.natCast_eq_natCast_iff']
    simpa only [Nat.cast_pow] using hf.pow_eq_pow_iff_modEq (n := a) (m := b)

private theorem success_to_good (N : ℕ) (hN : 1 < N) (ho : Odd N)
    (u : (ZMod N)ˣ) (hu : ShorAlgorithms.Reduction.successEvent N u) :
    2 ≤ (u : ZMod N).val ∧ (u : ZMod N).val ≤ N - 1 ∧
      Nat.Coprime (u : ZMod N).val N ∧
      Even (orderOf ((u : ZMod N).val : ZMod N)) ∧
      ¬ N ∣ (u : ZMod N).val ^ (orderOf ((u : ZMod N).val : ZMod N) / 2) + 1 ∧
      ¬ N ∣ (u : ZMod N).val ^ (orderOf ((u : ZMod N).val : ZMod N) / 2) - 1 := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨hN⟩
  have hc := ZMod.val_coe_unit_coprime u
  have hor : orderOf ((u : ZMod N).val : ZMod N) = orderOf u := by
    rw [ZMod.natCast_zmod_val, orderOf_units]
  have he : Even (orderOf u) := hu.1
  have hlt := ZMod.val_lt (u : ZMod N)
  have hval : 2 ≤ (u : ZMod N).val := by
    have hz : (u : ZMod N).val ≠ 0 := by
      intro hz
      simp only [hz, Nat.coprime_zero_left] at hc
      omega
    have hone : (u : ZMod N).val ≠ 1 := by
      intro hv
      have hcoe : (u : ZMod N) = 1 := by
        have := congrArg (fun n : ℕ => (n : ZMod N)) hv
        simpa using this
      have huone : u = 1 := Units.ext hcoe
      simpa [huone] using he
    omega
  refine ⟨hval, by omega, hc, hor ▸ he, ?_, ?_⟩
  · intro hd
    have hcast : (u : ZMod N) ^ (orderOf u / 2) = -1 := by
      have hz := (ZMod.natCast_eq_zero_iff
        ((u : ZMod N).val ^ (orderOf ((u : ZMod N).val : ZMod N) / 2) + 1) N).2 hd
      push_cast at hz
      rw [ZMod.natCast_zmod_val, orderOf_units] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hnegval : (-1 : ZMod N).val = N - 1 := by
      cases N with
      | zero => omega
      | succ n => simpa using ZMod.val_neg_one n
    have hcop : Nat.Coprime (N - 2) N :=
      (Nat.coprime_self_sub_left (by omega : 2 ≤ N)).2 ho.coprime_two_left
    have hcand : ShorAlgorithms.Reduction.factorCandidate N u = 1 := by
      simp only [ShorAlgorithms.Reduction.factorCandidate, hcast, hnegval]
      simpa only [Nat.sub_sub] using hcop.gcd_eq_one
    have := hu.2.1
    omega
  · intro hd
    have hz := (ZMod.natCast_eq_zero_iff
      ((u : ZMod N).val ^ (orderOf ((u : ZMod N).val : ZMod N) / 2) - 1) N).2 hd
    have hxpos : 1 ≤ (u : ZMod N).val ^
        (orderOf ((u : ZMod N).val : ZMod N) / 2) := one_le_pow₀ (by omega)
    rw [Nat.cast_sub hxpos, Nat.cast_pow, ZMod.natCast_zmod_val, orderOf_units,
      Nat.cast_one, sub_eq_zero] at hz
    have hcand : ShorAlgorithms.Reduction.factorCandidate N u = N := by
      simp only [ShorAlgorithms.Reduction.factorCandidate, hz, ZMod.val_one,
        Nat.sub_self, Nat.gcd_zero_left]
    have := hu.2.2
    omega

private theorem good_card_bound (N : ℕ) (hN : 1 < N) (ho : Odd N) (hpp : ¬ IsPrimePow N) :
    ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N).card ≤
      2 * ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N ∧
        Even (orderOf (x : ZMod N)) ∧ ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 ∧
        ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1).card := by
  classical
  letI : NeZero N := ⟨by omega⟩
  let good := (Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N ∧
    Even (orderOf (x : ZMod N)) ∧ ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 ∧
    ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1
  let f : {u : (ZMod N)ˣ // ShorAlgorithms.Reduction.successEvent N u} →
      {x : ℕ // x ∈ good} := fun u => ⟨(u.val : ZMod N).val, by
    obtain ⟨hl, hr, hc, he, hp, hm⟩ := success_to_good N hN ho u.val u.property
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hr⟩, hc, he, hp, hm⟩⟩
  have hfinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective N
    exact congrArg Subtype.val huv
  have hcount : Nat.card {u : (ZMod N)ˣ // ShorAlgorithms.Reduction.successEvent N u} ≤
      good.card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective f hfinj
  have hprime : 2 ≤ N.primeFactors.card := by
    have := (Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega : 2 ≤ N)).1 hpp
    exact Finset.one_lt_card_iff_nontrivial.mpr this
  have hpow : (2 : ℝ) ≤ 2 ^ (N.primeFactors.card - 1) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ N.primeFactors.card - 1 by omega)
  have hfrac : (1 : ℝ) / 2 ^ (N.primeFactors.card - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpow
  have hprob := ShorAlgorithms.Reduction.factor_prob_ge N ho hN
  have hphi : (Nat.totient N : ℝ) ≤ 2 * good.card := by
    have hc : (Nat.card {u : (ZMod N)ˣ // ShorAlgorithms.Reduction.successEvent N u} : ℝ) ≤
        good.card := by exact_mod_cast hcount
    have hnonneg : (0 : ℝ) ≤ Nat.totient N := Nat.cast_nonneg _
    nlinarith
  have hcopcount : ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N).card ≤
      Nat.totient N := by
    rw [Nat.totient_eq_card_coprime]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2.symm⟩
  exact hcopcount.trans (by exact_mod_cast hphi)

theorem solution (N : ℕ) (hN : 1 < N) (hodd : Odd N)
    (hpp : ¬ IsPrimePow N) :
    (∀ x ∈ Finset.Icc 2 (N - 1), ¬ Nat.Coprime x N → 1 < Nat.gcd x N ∧ Nat.gcd x N < N) ∧
    (∀ x : ℕ, Nat.Coprime x N →
      0 < orderOf (x : ZMod N) ∧ orderOf (x : ZMod N) ≤ N ∧
        HasPeriod (fun a => x ^ a % N) (orderOf (x : ZMod N))) ∧
    (∀ x ∈ Finset.Icc 2 (N - 1), Nat.Coprime x N → Even (orderOf (x : ZMod N)) →
      ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 → ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1 →
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N < N) ∧
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N < N)) ∧
    ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N).card ≤
      2 * ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N ∧
        Even (orderOf (x : ZMod N)) ∧ ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 ∧
        ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1).card := by
  refine ⟨?_, ?_, ?_, good_card_bound N hN hodd hpp⟩
  · intro x hx hnc
    obtain ⟨hxl, hxr⟩ := Finset.mem_Icc.mp hx
    have hxpos : 0 < x := by omega
    have hgpos := Nat.gcd_pos_of_pos_left N hxpos
    have hgne : Nat.gcd x N ≠ 1 := hnc
    refine ⟨by omega, ?_⟩
    exact (Nat.gcd_le_left N hxpos).trans_lt (by omega)
  · intro x hc
    exact period_of_coprime N x hN hc
  · intro x hx hc he hp _hm
    obtain ⟨hxl, hxr⟩ := Finset.mem_Icc.mp hx
    have hg := ShorWiki.gcd_pow_half_nontrivial N x (by omega) (by omega) hc he hp
    simpa only [ShorWiki.ord, Nat.gcd_comm] using And.intro hg.2 hg.1
