-- Prove2me | solution 1 for SecretaryWD.DiscUpper.top_classes_carry_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:32:10.651833+00:00
-- url     : https://prove2.me/submissions/3b78cc73-6508-46d1-bba1-ae6f324070a0

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

set_option autoImplicit false

namespace P62e12681

open SecretaryWD.DiscUpper

lemma sum_perm_eval {n : ℕ} (w : Fin n → ℝ) (t0 : Fin n) :
    (n : ℝ) * ∑ π : Equiv.Perm (Fin n), w (π t0) = (n.factorial : ℝ) * ∑ e, w e := by
  have h1 : ∀ s : Fin n, ∑ π : Equiv.Perm (Fin n), w (π t0)
      = ∑ π : Equiv.Perm (Fin n), w (π s) := by
    intro s
    exact (Fintype.sum_equiv (Equiv.mulRight (Equiv.swap s t0)) (fun π => w (π s))
      (fun π => w (π t0)) (by intro π; simp [Equiv.Perm.mul_apply])).symm
  calc (n : ℝ) * ∑ π : Equiv.Perm (Fin n), w (π t0)
      = ∑ _s : Fin n, ∑ π : Equiv.Perm (Fin n), w (π t0) := by simp
    _ = ∑ s : Fin n, ∑ π : Equiv.Perm (Fin n), w (π s) :=
        Finset.sum_congr rfl (fun s _ => h1 s)
    _ = ∑ π : Equiv.Perm (Fin n), ∑ s : Fin n, w (π s) := Finset.sum_comm
    _ = ∑ _π : Equiv.Perm (Fin n), ∑ e, w e := by
        refine Finset.sum_congr rfl (fun π _ => ?_)
        exact Equiv.sum_comp π w
    _ = (n.factorial : ℝ) * ∑ e, w e := by simp [Fintype.card_perm]

lemma exists_optTime {n : ℕ} (hn : 1 ≤ n) (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ∃ t, IsOptTime d v π t ∧ optValue d v π = d t * v (π t) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨t1, ht1⟩ := Finite.exists_max (fun t => d t * v (π t))
  have hne : (Finset.univ.filter (fun t => d t * v (π t) = d t1 * v (π t1))).Nonempty :=
    ⟨t1, by simp⟩
  set tm := (Finset.univ.filter (fun t => d t * v (π t) = d t1 * v (π t1))).min' hne with htm
  have hmem := Finset.min'_mem _ hne
  rw [← htm] at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨tm, ⟨fun s => ?_, fun s hs => ?_⟩, ?_⟩
  · rw [hmem]; exact ht1 s
  · rw [hmem]
    refine lt_of_le_of_ne (ht1 s) (fun heq => ?_)
    have : tm ≤ s := Finset.min'_le _ s (by simp [heq])
    exact absurd hs (not_lt.2 this)
  · unfold optValue
    apply le_antisymm
    · exact ciSup_le fun s => by rw [hmem]; exact ht1 s
    · exact le_ciSup (Finite.bddAbove_range (fun t => d t * v (π t))) tm

open Classical in
lemma pointwise {n : ℕ} (hn : 1 ≤ n) (d v : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hv : ∀ e, 0 ≤ v e) (K : ℕ) (π : Equiv.Perm (Fin n)) :
    optValue d v π ≤ (∑ c ∈ Finset.Icc 1 K, ∑ t ∈ discountClass d c,
      if IsOptTime d v π t then d t * v (π t) else 0) + dmax d / 2 ^ K * vmax v := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ts, hts, hopt⟩ := exists_optTime hn d v π
  have hdD : ∀ t, d t ≤ dmax d := fun t => le_ciSup (Finite.bddAbove_range d) t
  have hvV : ∀ e, v e ≤ vmax v := fun e => le_ciSup (Finite.bddAbove_range v) e
  have hD0 : 0 ≤ dmax d := le_trans (hd ts) (hdD ts)
  have hV0 : 0 ≤ vmax v := le_trans (hv (π ts)) (hvV _)
  have hnn : ∀ t, 0 ≤ (if IsOptTime d v π t then d t * v (π t) else 0) := by
    intro t
    split_ifs
    · exact mul_nonneg (hd t) (hv _)
    · exact le_refl 0
  have herr : 0 ≤ dmax d / 2 ^ K * vmax v := by positivity
  have hSnn : 0 ≤ ∑ c ∈ Finset.Icc 1 K, ∑ t ∈ discountClass d c,
      (if IsOptTime d v π t then d t * v (π t) else 0) :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun t _ => hnn t
  by_cases hcase : dmax d / 2 ^ K < d ts
  · have hex : ∃ c : ℕ, dmax d / 2 ^ c < d ts := ⟨K, hcase⟩
    obtain ⟨c0, hc0spec, hc0min⟩ : ∃ c0 : ℕ, dmax d / 2 ^ c0 < d ts ∧
        ∀ m, m < c0 → ¬ dmax d / 2 ^ m < d ts :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hc0le : c0 ≤ K := by
      by_contra h
      exact hc0min K (by omega) hcase
    have hc0pos : c0 ≠ 0 := by
      intro h
      subst h
      simp at hc0spec
      linarith [hdD ts]
    obtain ⟨k, hk⟩ : ∃ k, c0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hc0pos
    have hkfail : ¬ dmax d / 2 ^ k < d ts := hc0min k (by omega)
    have hmem_c : c0 ∈ Finset.Icc 1 K := Finset.mem_Icc.2 ⟨by omega, hc0le⟩
    have hmem_t : ts ∈ discountClass d c0 := by
      simp only [discountClass, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hc0spec, ?_⟩
      rw [hk, pow_succ]
      have : 2 * dmax d / (2 ^ k * 2) = dmax d / 2 ^ k := by field_simp
      rw [this]
      exact not_lt.mp hkfail
    have h1 : (if IsOptTime d v π ts then d ts * v (π ts) else 0) ≤
        ∑ t ∈ discountClass d c0, (if IsOptTime d v π t then d t * v (π t) else 0) :=
      Finset.single_le_sum (f := fun t => if IsOptTime d v π t then d t * v (π t) else 0)
        (fun t _ => hnn t) hmem_t
    have h2 : ∑ t ∈ discountClass d c0, (if IsOptTime d v π t then d t * v (π t) else 0) ≤
        ∑ c ∈ Finset.Icc 1 K, ∑ t ∈ discountClass d c,
          (if IsOptTime d v π t then d t * v (π t) else 0) :=
      Finset.single_le_sum (f := fun c => ∑ t ∈ discountClass d c,
          (if IsOptTime d v π t then d t * v (π t) else 0))
        (fun c _ => Finset.sum_nonneg fun t _ => hnn t) hmem_c
    rw [if_pos hts] at h1
    rw [hopt]
    linarith
  · push_neg at hcase
    rw [hopt]
    have : d ts * v (π ts) ≤ dmax d / 2 ^ K * vmax v :=
      mul_le_mul hcase (hvV _) (hv _) (le_trans (hd ts) hcase)
    linarith

theorem main (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    expectedOpt d v / 2 ≤ ∑ c ∈ Finset.Icc 1 (3 * Nat.clog 2 n + 1), optClass d v c := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set K := 3 * Nat.clog 2 n + 1 with hK
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := d)
  obtain ⟨e0, he0⟩ := exists_eq_ciSup_of_finite (f := v)
  have hD : dmax d = d t0 := ht0.symm
  have hV : vmax v = v e0 := he0.symm
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hfac : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  -- lower bound on E[OPT]
  have hE : dmax d * vmax v ≤ n * expectedOpt d v := by
    have hlow : ∀ π : Equiv.Perm (Fin n), d t0 * v (π t0) ≤ optValue d v π := fun π =>
      le_ciSup (Finite.bddAbove_range (fun t => d t * v (π t))) t0
    have hsum : ∑ π : Equiv.Perm (Fin n), d t0 * v (π t0) ≤
        ∑ π : Equiv.Perm (Fin n), optValue d v π :=
      Finset.sum_le_sum (fun π _ => hlow π)
    rw [← Finset.mul_sum] at hsum
    have hperm := sum_perm_eval v t0
    have hvsum : v e0 ≤ ∑ e, v e := Finset.single_le_sum (fun e _ => hv e) (Finset.mem_univ e0)
    have key : (n.factorial : ℝ) * (d t0 * v e0) ≤ n * ∑ π : Equiv.Perm (Fin n), optValue d v π := by
      calc (n.factorial : ℝ) * (d t0 * v e0) ≤ (n.factorial : ℝ) * (d t0 * ∑ e, v e) := by
            have := hd t0
            gcongr
        _ = d t0 * ((n : ℝ) * ∑ π : Equiv.Perm (Fin n), v (π t0)) := by rw [hperm]; ring
        _ = (n : ℝ) * (d t0 * ∑ π : Equiv.Perm (Fin n), v (π t0)) := by ring
        _ ≤ n * ∑ π : Equiv.Perm (Fin n), optValue d v π :=
            mul_le_mul_of_nonneg_left hsum hnpos.le
    unfold expectedOpt uniformAvg
    rw [hD, hV]
    rw [show (n : ℝ) * (1 / (n.factorial : ℝ) * ∑ π : Equiv.Perm (Fin n), optValue d v π)
        = ((n : ℝ) * ∑ π : Equiv.Perm (Fin n), optValue d v π) / n.factorial by ring,
      le_div_iff₀ hfac]
    linarith
  -- 2n ≤ 2^K
  have h2n : (2 * n : ℝ) ≤ 2 ^ K := by
    have h1 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
    have h3 : 2 ^ Nat.clog 2 n ≤ (2 ^ 3) ^ Nat.clog 2 n := Nat.pow_le_pow_left (by norm_num) _
    have h2 : 2 * n ≤ 2 ^ K := by
      rw [hK, pow_succ, pow_mul]
      calc 2 * n ≤ 2 * (2 ^ 3) ^ Nat.clog 2 n := by omega
        _ = (2 ^ 3) ^ Nat.clog 2 n * 2 := by ring
    exact_mod_cast h2
  -- linearity
  have hsumc : ∑ c ∈ Finset.Icc 1 K, optClass d v c =
      (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n), (∑ c ∈ Finset.Icc 1 K,
        ∑ t ∈ discountClass d c, if IsOptTime d v π t then d t * v (π t) else 0) := by
    unfold optClass uniformAvg
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hpt : ∑ π : Equiv.Perm (Fin n), optValue d v π ≤
      ∑ π : Equiv.Perm (Fin n), ((∑ c ∈ Finset.Icc 1 K,
        ∑ t ∈ discountClass d c, if IsOptTime d v π t then d t * v (π t) else 0)
          + dmax d / 2 ^ K * vmax v) :=
    Finset.sum_le_sum (fun π _ => by convert pointwise hn d v hd hv K π)
  rw [Finset.sum_add_distrib] at hpt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hpt
  rw [hsumc]
  set S := ∑ π : Equiv.Perm (Fin n), (∑ c ∈ Finset.Icc 1 K,
        ∑ t ∈ discountClass d c, if IsOptTime d v π t then d t * v (π t) else 0) with hS
  set q := dmax d * vmax v with hq
  have hq0 : 0 ≤ q := by
    rw [hq, hD, hV]
    exact mul_nonneg (hd t0) (hv e0)
  have hE1 : expectedOpt d v ≤ 1 / (n.factorial : ℝ) * S + dmax d / 2 ^ K * vmax v := by
    unfold expectedOpt uniformAvg
    have : 1 / (n.factorial : ℝ) * (S + (n.factorial : ℝ) * (dmax d / 2 ^ K * vmax v))
        = 1 / (n.factorial : ℝ) * S + dmax d / 2 ^ K * vmax v := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hpt (by positivity)
  have herr : dmax d / 2 ^ K * vmax v ≤ expectedOpt d v / 2 := by
    have e1 : dmax d / 2 ^ K * vmax v = q / 2 ^ K := by rw [hq]; ring
    rw [e1]
    have h2npos : (0:ℝ) < 2 * n := by positivity
    calc q / 2 ^ K ≤ q / (2 * n) := div_le_div_of_nonneg_left hq0 h2npos h2n
      _ ≤ expectedOpt d v / 2 := by
        rw [div_le_iff₀ h2npos]
        nlinarith
  linarith

end P62e12681

open SecretaryWD.DiscUpper in
theorem solution (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    expectedOpt d v / 2 ≤ ∑ c ∈ Finset.Icc 1 (3 * Nat.clog 2 n + 1), optClass d v c := by
  exact P62e12681.main n hn d v hd hv
