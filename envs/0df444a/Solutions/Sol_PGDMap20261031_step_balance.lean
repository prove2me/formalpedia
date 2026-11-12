-- Prove2me | solution 1 for PGDMap20261031.step_balance
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T14:44:19.726373+00:00
-- url     : https://prove2.me/submissions/0412a186-1c4e-48bc-9f43-bf6a84a90bfb

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_PGDMap20261031_Stepsize

open PGDMap20261031
noncomputable section

private lemma even_power (h : ℝ) (k : ℕ) : (1 - h) ^ (2 * k) = (h - 1) ^ (2 * k) := by
  rw [pow_mul, pow_mul]
  congr 1
  ring

private lemma denominatorA_pos (N : ℕ) (h q : ℝ) (hN : 1 ≤ N)
    (hh : validStep h) (hq : 0 < q) : 0 < (base h q) ^ (2 * N) - 1 - h ^ 2 * q := by
  have hb : 1 ≤ base h q := by unfold base; nlinarith [hh.1]
  have hpow : (base h q) ^ 2 ≤ (base h q) ^ (2 * N) :=
    pow_le_pow_right₀ hb (by omega)
  have hinner : 0 < 2 - h + h * q := by nlinarith [hh.1, hh.2]
  have hprod := mul_pos (mul_pos hh.1 hq) hinner
  dsimp [base] at hpow ⊢
  nlinarith only [hpow, hprod]

private lemma denominatorB_pos (N : ℕ) (h q : ℝ) (hN : 1 ≤ N)
    (hh : validStep h) (hq : 0 ≤ q) : 0 < (base h q) ^ (2 * N) - (1 - h) ^ (2 * N) := by
  have hb : 1 ≤ base h q := by unfold base; nlinarith [hh.1]
  have habs : |1 - h| < 1 := abs_lt.mpr ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have hp : |1 - h| ^ (2 * N) < 1 := pow_lt_one₀ (abs_nonneg _) habs (by omega)
  have hp' : (1 - h) ^ (2 * N) < 1 := lt_of_le_of_lt (le_abs_self _) (by simpa [abs_pow] using hp)
  linarith [one_le_pow₀ hb (n := 2 * N)]

private lemma branchA_strictAnti (N : ℕ) (q : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q) :
    StrictAntiOn (fun h => branchA N h q) (Set.Ioo (0 : ℝ) 2) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hzero : q = 0
  · subst q
    have hD : StrictMonoOn (fun h : ℝ => h * (2 * (N : ℝ) - h)) (Set.Ioo 0 2) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 2) (by fun_prop)
      intro h hh
      have ht : h ∈ Set.Ioo (0 : ℝ) 2 := by simpa using hh
      have hd : HasDerivAt (fun h : ℝ => h * (2 * (N : ℝ) - h))
          (2 * (N : ℝ) - 2 * h) h := by
        convert (hasDerivAt_id h).mul ((hasDerivAt_id h).const_sub (2 * (N : ℝ))) using 1
          <;> try rfl
        simp only [id_eq]
        ring
      rw [hd.deriv]
      linarith [ht.2]
    intro x hx y hy hxy
    have hdx : 0 < x * (2 * (N : ℝ) - x) := mul_pos hx.1 (by linarith [hx.2])
    have hdy : 0 < y * (2 * (N : ℝ) - y) := mul_pos hy.1 (by linarith [hy.2])
    simp only [branchA]
    apply (div_lt_div_iff₀ hdy hdx).2
    linarith only [hD hx hy hxy]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    have hD : StrictMonoOn (fun h : ℝ => (base h q) ^ (2 * N) - 1 - h ^ 2 * q)
        (Set.Ioo 0 2) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 2)
        (by unfold base; fun_prop)
      intro h hh
      have ht : h ∈ Set.Ioo (0 : ℝ) 2 := by simpa using hh
      have hd : HasDerivAt (fun h : ℝ => (base h q) ^ (2 * N) - 1 - h ^ 2 * q)
          (2 * q * ((N : ℝ) * (base h q) ^ (2 * N - 1) - h)) h := by
        convert (((((hasDerivAt_id h).mul_const q).const_add 1).pow (2 * N)).sub_const 1).sub
          (((hasDerivAt_id h).pow 2).mul_const q) using 1 <;> try rfl
        simp only [base, id_eq, Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [hd.deriv]
      have hb : 1 ≤ base h q := by unfold base; nlinarith [ht.1]
      have hbp := one_le_pow₀ hb (n := 2 * N - 1)
      have hinner : 0 < (N : ℝ) * (base h q) ^ (2 * N - 1) - h := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ (N : ℝ)) (sub_nonneg.mpr hbp), ht.2]
      exact mul_pos (mul_pos (by norm_num) hqp) hinner
    intro x hx y hy hxy
    simp only [branchA, if_neg hzero]
    apply (div_lt_div_iff₀
      (denominatorA_pos N y q (by omega) hy hqp)
      (denominatorA_pos N x q (by omega) hx hqp)).2
    have hdiff := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hqp)
      (sub_pos.mpr (hD hx hy hxy))
    nlinarith only [hdiff]

private lemma pow_deriv_div (f : ℝ → ℝ) (f' t : ℝ) (n : ℕ)
    (hf : HasDerivAt f f' t) (hn : 1 ≤ n) (hne : f t ≠ 0) :
    HasDerivAt (fun t => f t ^ n) ((n : ℝ) * f t ^ n * f' / f t) t := by
  convert hf.pow n using 1 <;> try rfl
  rw [pow_sub₀ (f t) hne hn]
  simp only [pow_one]
  ring

private def risingB (k : ℕ) (q h : ℝ) : ℝ :=
  2 * (1 + q) * (h - 1) ^ (2 * k) /
    ((base h q) ^ (2 * k + 2) - (h - 1) ^ (2 * k + 2))

private lemma risingB_hasDerivAt (k : ℕ) (q h : ℝ) (hk : 1 ≤ k)
    (hq : 0 ≤ q) (hh : h ∈ Set.Ioo (1 : ℝ) 2) :
    HasDerivAt (risingB k q)
      (risingB k q h * 2 * ((base h q) ^ (2 * k + 1) *
        ((k : ℝ) * (1 + q) - q * (h - 1)) + (h - 1) ^ (2 * k + 2)) /
        ((h - 1) * ((base h q) ^ (2 * k + 2) - (h - 1) ^ (2 * k + 2)))) h := by
  have htpos : 0 < h - 1 := by linarith [hh.1]
  have hb : 1 ≤ base h q := by unfold base; nlinarith [hh.1]
  have hbpos : 0 < base h q := by linarith
  have hden : 0 < (base h q) ^ (2 * k + 2) - (h - 1) ^ (2 * k + 2) := by
    have hp := pow_lt_one₀ htpos.le (by linarith [hh.2] : h - 1 < 1) (n := 2 * k + 2) (by omega)
    linarith [one_le_pow₀ hb (n := 2 * k + 2)]
  have hdT : HasDerivAt (fun h : ℝ => h - 1) 1 h := (hasDerivAt_id h).sub_const 1
  have hdB : HasDerivAt (fun h : ℝ => base h q) q h := by
    convert ((hasDerivAt_id h).mul_const q).const_add 1 using 1 <;> first | rfl | simp
  have hT := pow_deriv_div _ _ _ (2 * k) hdT (by omega) htpos.ne'
  have hT2 := pow_deriv_div _ _ _ (2 * k + 2) hdT (by omega) htpos.ne'
  have hB2 := pow_deriv_div _ _ _ (2 * k + 2) hdB (by omega) hbpos.ne'
  convert (hT.const_mul (2 * (1 + q))).div (hB2.sub hT2) hden.ne' using 1 <;> try rfl
  unfold risingB
  simp only [Pi.sub_apply,
    pow_add, pow_one, pow_two, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_one] at hden ⊢
  field_simp [ne_of_gt hden, htpos.ne', hbpos.ne']
  unfold base
  ring

private lemma branchB_strictMono (N : ℕ) (q : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q) :
    StrictMonoOn (fun h => branchB N h q) (Set.Ioo (1 : ℝ) 2) := by
  let k := N - 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hm : 2 * N = 2 * k + 2 := by dsimp [k]; omega
  have hm2 : 2 * N - 2 = 2 * k := by dsimp [k]; omega
  have hB : (fun h => branchB N h q) = risingB k q := by
    funext h
    unfold branchB risingB
    rw [hm2, hm, even_power h k, show 2 * k + 2 = 2 * (k + 1) by omega,
      even_power h (k + 1)]
  rw [hB]
  apply strictMonoOn_of_deriv_pos (convex_Ioo 1 2)
  · intro h hh
    exact (risingB_hasDerivAt k q h hk hq hh).continuousAt.continuousWithinAt
  · intro h hh
    have ht : h ∈ Set.Ioo (1 : ℝ) 2 := by simpa using hh
    rw [(risingB_hasDerivAt k q h hk hq ht).deriv]
    have htpos : 0 < h - 1 := by linarith [ht.1]
    have hb : 1 ≤ base h q := by unfold base; nlinarith [ht.1]
    have hbpos : 0 < base h q := by linarith
    have hden : 0 < (base h q) ^ (2 * k + 2) - (h - 1) ^ (2 * k + 2) := by
      have hp := pow_lt_one₀ htpos.le (by linarith [ht.2] : h - 1 < 1) (n := 2 * k + 2) (by omega)
      linarith [one_le_pow₀ hb (n := 2 * k + 2)]
    have hBpos : 0 < risingB k q h := by
      unfold risingB
      exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (pow_pos htpos _)) hden
    have hcoef : 0 < (k : ℝ) * (1 + q) - q * (h - 1) := by
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_nonneg (sub_nonneg.mpr hkr) hq, mul_nonneg hq (by linarith [ht.2] : 0 ≤ 2 - h)]
    exact div_pos (mul_pos (mul_pos hBpos (by norm_num))
      (add_pos (mul_pos (pow_pos hbpos _) hcoef) (pow_pos htpos _))) (mul_pos htpos hden)

private def crossingPolynomial (N : ℕ) (q h : ℝ) : ℝ :=
  if q = 0 then (h - 1) ^ (2 * (N - 1)) * (1 + 2 * ((N - 1 : ℕ) : ℝ) * h) - 1
  else (h - 1) ^ (2 * (N - 1)) * ((1 + q) * (base h q) ^ (2 * (N - 1)) - 1) -
    q * (base h q) ^ (2 * (N - 1))

private lemma crossing_iff (N : ℕ) (q h : ℝ) (hN : 2 ≤ N)
    (hq : 0 ≤ q) (hh : h ∈ Set.Ioo (1 : ℝ) 2) :
    branchA N h q = branchB N h q ↔ crossingPolynomial N q h = 0 := by
  let k := N - 1
  have hm : 2 * N = 2 * k + 2 := by dsimp [k]; omega
  have hm2 : 2 * N - 2 = 2 * k := by dsimp [k]; omega
  have hNr : (N : ℝ) = (k : ℝ) + 1 := by exact_mod_cast (show N = k + 1 by dsimp [k]; omega)
  have hNrlo : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hv : validStep h := ⟨by linarith [hh.1], hh.2⟩
  have hdb := denominatorB_pos N h q (by omega) hv hq
  by_cases hz : q = 0
  · subst q
    have hda : 0 < h * (2 * (N : ℝ) - h) := mul_pos hv.1 (by linarith [hh.2])
    simp only [base, mul_zero, add_zero, one_pow] at hdb
    rw [even_power h N] at hdb
    simp only [hm, pow_add, pow_two] at hdb
    simp only [branchA, branchB]
    simp only [base, mul_zero, add_zero, one_pow, mul_one]
    simp only [ite_true]
    rw [hm2, even_power h k, even_power h N]
    simp only [hm, pow_add, pow_two]
    rw [div_eq_div_iff hda.ne' hdb.ne']
    unfold crossingPolynomial
    rw [if_pos (rfl : (0 : ℝ) = 0)]
    change _ ↔ (h - 1) ^ (2 * k) * (1 + 2 * (k : ℝ) * h) - 1 = 0
    have hid : 2 * (1 - (h - 1) ^ (2 * k) * ((h - 1) * (h - 1))) -
        (2 * (h - 1) ^ (2 * k)) * (h * (2 * (N : ℝ) - h)) =
        -2 * ((h - 1) ^ (2 * k) * (1 + 2 * (k : ℝ) * h) - 1) := by
      rw [hNr]
      ring
    constructor <;> intro heq <;> linarith only [hid, heq]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    have hda := denominatorA_pos N h q (by omega) hv hqp
    simp only [branchA, branchB, if_neg hz]
    rw [hm2, even_power h k, even_power h N]
    rw [even_power h N] at hdb
    simp only [hm, pow_add, pow_two] at hda hdb ⊢
    rw [div_eq_div_iff hda.ne' hdb.ne']
    unfold crossingPolynomial
    rw [if_neg hz]
    change _ ↔ (h - 1) ^ (2 * k) * ((1 + q) * (base h q) ^ (2 * k) - 1) -
      q * (base h q) ^ (2 * k) = 0
    let P := (h - 1) ^ (2 * k) * ((1 + q) * (base h q) ^ (2 * k) - 1) -
      q * (base h q) ^ (2 * k)
    have hid : 2 * q * ((base h q) ^ (2 * k) * (base h q * base h q) -
        (h - 1) ^ (2 * k) * ((h - 1) * (h - 1))) -
        (2 * (1 + q) * (h - 1) ^ (2 * k)) *
          ((base h q) ^ (2 * k) * (base h q * base h q) - 1 - h * h * q) =
        (-2 * (base h q) ^ 2) * P := by
      dsimp [P, base]
      ring
    have hfactor : -2 * (base h q) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (by unfold base; nlinarith [hv.1]))
    constructor
    · intro heq
      exact (mul_eq_zero.mp (show (-2 * (base h q) ^ 2) * P = 0 by
        linarith only [hid, heq])).resolve_left hfactor
    · intro heq
      have hP : P = 0 := heq
      rw [hP, mul_zero] at hid
      linarith only [hid]

private lemma crossing_exists (N : ℕ) (q : ℝ) (hN : 2 ≤ N) (hq : 0 ≤ q) :
    ∃ h ∈ Set.Ioo (1 : ℝ) 2, branchA N h q = branchB N h q := by
  have hk : 1 ≤ N - 1 := by omega
  have hkr : (1 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hk
  have hnzero : 2 * (N - 1) ≠ 0 := by omega
  have hcont : ContinuousOn (crossingPolynomial N q) (Set.Icc (1 : ℝ) 2) := by
    unfold crossingPolynomial
    split_ifs <;> (try dsimp only [base]) <;> fun_prop
  have hleft : crossingPolynomial N q 1 < 0 := by
    by_cases hz : q = 0
    · norm_num [crossingPolynomial, hz, hnzero]
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      simp only [crossingPolynomial, if_neg hz, sub_self, zero_pow hnzero, zero_mul, zero_sub]
      exact neg_neg_of_pos (mul_pos hqp (pow_pos (by unfold base; linarith) _))
  have hright : 0 < crossingPolynomial N q 2 := by
    by_cases hz : q = 0
    · simp only [crossingPolynomial, if_pos hz]
      norm_num
      linarith
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      have hp : 1 < (1 + 2 * q) ^ (2 * (N - 1)) := by
        simpa using pow_lt_pow_left₀ (by linarith : (1 : ℝ) < 1 + 2 * q)
          (by norm_num : (0 : ℝ) ≤ 1) hnzero
      have heq : crossingPolynomial N q 2 = (1 + 2 * q) ^ (2 * (N - 1)) - 1 := by
        simp only [crossingPolynomial, if_neg hz, base]
        norm_num
        ring
      rw [heq]
      linarith only [hp]
  obtain ⟨h, hh, heq⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont
    (show (0 : ℝ) ∈ Set.Icc (crossingPolynomial N q 1) (crossingPolynomial N q 2)
      from ⟨hleft.le, hright.le⟩)
  have hh' : h ∈ Set.Ioo (1 : ℝ) 2 := by
    constructor
    · apply lt_of_le_of_ne hh.1
      intro he
      rw [he, heq] at hleft
      exact lt_irrefl _ hleft
    · apply lt_of_le_of_ne hh.2
      intro he
      rw [← he, heq] at hright
      exact lt_irrefl _ hright
  exact ⟨h, hh', (crossing_iff N q h hN hq hh').mpr heq⟩

theorem solution : StepBalanceClaim := by
  intro N q hN hq
  have hA := branchA_strictAnti N q hN hq
  have hB := branchB_strictMono N q hN hq
  obtain ⟨s, hs, hcross⟩ := crossing_exists N q hN hq
  have hvs : s ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hs.1], hs.2⟩
  have huniq (u : ℝ) (hu : u ∈ Set.Ioo (1 : ℝ) 2)
      (huCross : branchA N u q = branchB N u q) : u = s := by
    have hvu : u ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hu.1], hu.2⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [hA hvu hvs hlt, hB hu hs hlt]
    · linarith [hA hvs hvu hgt, hB hs hu hgt]
  have hset : {h : ℝ | 1 < h ∧ h < 2 ∧ branchA N h q = branchB N h q} = {s} := by
    ext h
    constructor
    · rintro ⟨hlo, hhi, heq⟩
      exact huniq h ⟨hlo, hhi⟩ heq
    · intro heq
      have : h = s := heq
      subst h
      exact ⟨hs.1, hs.2, hcross⟩
  have hsopt : optimalStep N q = s := by
    unfold optimalStep
    rw [hset, csInf_singleton]
  rw [hsopt]
  refine ⟨hs.1, hs.2, ⟨hvs, ?_⟩, hcross, ?_⟩
  · intro u hu hne
    have hNne : N ≠ 1 := by omega
    simp only [curve, if_neg hNne]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [← hcross, max_self]
      exact lt_of_lt_of_le (hA hu hvs hlt) (le_max_left _ _)
    · rw [hcross, max_self]
      have hu' : u ∈ Set.Ioo (1 : ℝ) 2 := ⟨lt_trans hs.1 hgt, hu.2⟩
      exact lt_of_lt_of_le (hB hs hu' hgt) (le_max_right _ _)
  · intro h hlo hhi heq
    exact huniq h ⟨hlo, hhi⟩ heq
