-- Prove2me | solution 1 for SymPolyOpt.PowerSumUB.newtonSum_affine
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:07:34.622206+00:00
-- url     : https://prove2.me/submissions/443ff50e-7ebd-435e-97e4-663f3a26ca73

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

set_option autoImplicit false

open Polynomial SymPolyOpt.PowerSumUB

theorem spu_rec (m : ℕ) (c : ℕ → ℂ) (R : Multiset ℂ)
    (hroot : ∀ z ∈ R, z ^ m + ∑ i ∈ Finset.range m, c i * z ^ i = 0) (k : ℕ) (hk : m ≤ k) :
    (R.map (· ^ k)).sum + ∑ i ∈ Finset.range m, c i * (R.map (· ^ (k - m + i))).sum = 0 := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    have ha := hroot a (Multiset.mem_cons_self a R)
    have ih' := ih fun z hz => hroot z (Multiset.mem_cons_of_mem hz)
    have h1 : a ^ k + ∑ i ∈ Finset.range m, c i * a ^ (k - m + i) = 0 := by
      have : a ^ k + ∑ i ∈ Finset.range m, c i * a ^ (k - m + i) = a ^ (k - m) * (a ^ m + ∑ i ∈ Finset.range m, c i * a ^ i) := by
        rw [mul_add, ← pow_add, Nat.sub_add_cancel hk, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]; ring
      rw [this, ha, mul_zero]
    simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib]
    linear_combination h1 + ih'

theorem spu_root_eq (m : ℕ) (p : ℝ[X]) (hp : p.Monic) (hdeg : p.natDegree = m) (z : ℂ)
    (hz : z ∈ p.aroots ℂ) :
    z ^ m + ∑ i ∈ Finset.range m, ((p.coeff i : ℝ) : ℂ) * z ^ i = 0 := by
  have h := ((Polynomial.mem_aroots.mp hz).2)
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at h
  have hc : p.coeff m = 1 := by rw [← hdeg]; exact hp.coeff_natDegree
  rw [hc] at h
  simp only [Complex.real_smul] at h
  rw [add_comm]
  simpa using h

theorem spu_part_a (m : ℕ) (p : ℝ[X]) (hp : p.Monic) (hdeg : p.natDegree = m) :
    ∀ k : ℕ, m ≤ k →
      newtonSum p k + ∑ i ∈ Finset.range m, p.coeff i * newtonSum p (k - m + i) = 0 := by
  intro k hk
  have h := spu_rec m (fun i => ((p.coeff i : ℝ) : ℂ)) (p.aroots ℂ)
    (fun z hz => spu_root_eq m p hp hdeg z hz) k hk
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.zero_re] at this
  unfold newtonSum
  exact this

theorem spu_part_b (m : ℕ) (p : ℝ[X]) (hp : p.Monic) (hdeg : p.natDegree = m) :
    ∀ k : ℕ, 1 ≤ k → k < m →
      newtonSum p k + ∑ i ∈ Finset.Ico 1 k, p.coeff (m - i) * newtonSum p (k - i) =
        -(k : ℝ) * p.coeff (m - k) := by
  intro k hk1 hkm
  set R := p.aroots ℂ with hR
  set q : ℂ[X] := p.map (algebraMap ℝ ℂ) with hq
  have hqm : q.Monic := hp.map _
  have hqdeg : q.natDegree = m := by rw [hq, natDegree_map]; exact hdeg
  have hRq : R = q.roots := rfl
  have hcardq : Multiset.card q.roots = q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcard : Multiset.card R = m := by rw [hRq, hcardq, hqdeg]
  have he : ∀ j, j ≤ m → R.esymm j = (-1) ^ j * ((p.coeff (m - j) : ℝ) : ℂ) := by
    intro j hj
    have h := Polynomial.coeff_eq_esymm_roots_of_card (p := q) hcardq (k := m - j) (by omega)
    rw [hqm.leadingCoeff, hqdeg, show m - (m - j) = j by omega, one_mul, hq, coeff_map] at h
    have hh : ((p.coeff (m - j) : ℝ) : ℂ) = (-1) ^ j * R.esymm j := h
    rw [hh, ← mul_assoc, ← mul_pow]; simp
  have hex : ∃ f : Fin m → ℂ, Finset.univ.val.map f = R := by
    refine ⟨fun i => R.toList.get ⟨i, by rw [Multiset.length_toList, hcard]; exact i.2⟩, ?_⟩
    rw [Fin.univ_val_map]
    have : List.ofFn (fun i : Fin m => R.toList.get ⟨i, by rw [Multiset.length_toList, hcard]; exact i.2⟩) = R.toList := by
      apply List.ext_getElem <;> simp [Multiset.length_toList, hcard]
    rw [this]; exact Multiset.coe_toList R
  obtain ⟨f, hf⟩ := hex
  have hpsum : ∀ j, MvPolynomial.aeval f (MvPolynomial.psum (Fin m) ℂ j) = (R.map (· ^ j)).sum := by
    intro j
    rw [MvPolynomial.psum, map_sum]
    simp only [map_pow, MvPolynomial.aeval_X]
    rw [← hf, Multiset.map_map]
    rfl
  have hN := congrArg (MvPolynomial.aeval f) (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin m) ℂ k (by omega))
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hf, hpsum] at hN
  have hsum : ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
      (-1 : ℂ) ^ a.1 * R.esymm a.1 * (R.map (· ^ a.2)).sum
      = ∑ i ∈ Finset.Ico 1 k, ((p.coeff (m - i) : ℝ) : ℂ) * (R.map (· ^ (k - i))).sum := by
    rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ ?_
    · ext i; simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ico]; omega
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      rw [he i (by omega), ← mul_assoc, ← mul_pow]
      simp
  have hneg : (-1 : ℂ) ^ (k + 1) * (-1) ^ k = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨k, by ring⟩
  have hC : (R.map (· ^ k)).sum + ∑ i ∈ Finset.Ico 1 k,
        ((p.coeff (m - i) : ℝ) : ℂ) * (R.map (· ^ (k - i))).sum
      = (((-(k : ℝ) * p.coeff (m - k) : ℝ)) : ℂ) := by
    rw [hN, hsum, he k hkm.le]
    push_cast
    linear_combination ((k : ℂ) * ((p.coeff (m - k) : ℝ) : ℂ)) * hneg
  have hre := congrArg Complex.re hC
  simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  unfold newtonSum
  exact hre

theorem spu_s0 (m : ℕ) (p : ℝ[X]) (hdeg : p.natDegree = m) : newtonSum p 0 = m := by
  have hcard : Multiset.card (p.aroots ℂ) = m := by
    rw [Polynomial.aroots_def, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  unfold newtonSum
  simp [hcard]

def SPUvalid (m : ℕ) (γ : ℕ → ℝ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = m ∧ ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → newtonSum p i = γ i

theorem spu_coeff_det (m : ℕ) (γ : ℕ → ℝ) : ∀ k : ℕ, ∃ a : ℝ,
    1 ≤ k → k < m → ∀ p : ℝ[X], SPUvalid m γ p → p.coeff (m - k) = a := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    choose a ha using ih
    let a' : ℕ → ℝ := fun i => if h : i < k then a i h else 0
    have ha' : ∀ i, i < k → 1 ≤ i → i < m → ∀ p : ℝ[X], SPUvalid m γ p → p.coeff (m - i) = a' i := by
      intro i hi h1 h2 p hp
      simp only [a', dif_pos hi]
      exact ha i hi h1 h2 p hp
    refine ⟨-(γ k + ∑ i ∈ Finset.Ico 1 k, a' i * γ (k - i)) / k, fun hk1 hkm p hp => ?_⟩
    have hb := spu_part_b m p hp.1 hp.2.1 k hk1 hkm
    have hs1 : newtonSum p k = γ k := hp.2.2 k hk1 (by omega)
    have hs2 : ∑ i ∈ Finset.Ico 1 k, p.coeff (m - i) * newtonSum p (k - i)
        = ∑ i ∈ Finset.Ico 1 k, a' i * γ (k - i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      rw [ha' i hi'.2 hi'.1 (by omega) p hp, hp.2.2 (k - i) (by omega) (by omega)]
    rw [hs1, hs2] at hb
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
    linarith

theorem spu_affine_all (m : ℕ) (γ : ℕ → ℝ) (hm : 1 ≤ m) : ∀ j : ℕ, j ≤ 2 * m - 1 →
    ∃ a b : ℝ, (j < m → b = 0) ∧ ∀ p : ℝ[X], SPUvalid m γ p → newtonSum p j = a + b * p.coeff 0 := by
  choose dd hdd using spu_coeff_det m γ
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjm : j < m
    · by_cases hj0 : j = 0
      · subst hj0
        exact ⟨m, 0, fun _ => rfl, fun p hp => by rw [spu_s0 m p hp.2.1]; simp⟩
      · exact ⟨γ j, 0, fun _ => rfl, fun p hp => by
          rw [hp.2.2 j (by omega) (by omega)]; simp⟩
    · rw [not_lt] at hjm
      have ih' : ∀ t, ∃ a b : ℝ, t < j → ((t < m → b = 0) ∧ ∀ p : ℝ[X], SPUvalid m γ p → newtonSum p t = a + b * p.coeff 0) := by
        intro t
        by_cases ht : t < j
        · obtain ⟨a, b, h1, h2⟩ := ih t ht (by omega)
          exact ⟨a, b, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨0, 0, fun h => absurd h ht⟩
      choose α β hαβ using ih'
      have hm1 : m = (m - 1) + 1 := by omega
      refine ⟨-∑ i ∈ Finset.Ico 1 m, dd (m - i) * α (j - m + i),
        -α (j - m) - ∑ i ∈ Finset.Ico 1 m, dd (m - i) * β (j - m + i), fun h => absurd h (by omega), ?_⟩
      intro p hp
      have hpa := spu_part_a m p hp.1 hp.2.1 j hjm
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m)] at hpa
      have h0 := hαβ (j - m) (by omega)
      have hb0 : β (j - m) = 0 := h0.1 (by omega)
      have e0 : newtonSum p (j - m + 0) = α (j - m) := by
        rw [add_zero, h0.2 p hp, hb0]; simp
      have e1 : ∑ i ∈ Finset.Ico (0 + 1) m, p.coeff i * newtonSum p (j - m + i)
          = ∑ i ∈ Finset.Ico 1 m, dd (m - i) * (α (j - m + i) + β (j - m + i) * p.coeff 0) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_Ico.mp hi
        have hc : p.coeff i = dd (m - i) := by
          have := hdd (m - i) (by omega) (by omega) p hp
          rwa [show m - (m - i) = i by omega] at this
        rw [hc, (hαβ (j - m + i) (by omega)).2 p hp]
      rw [e0, e1] at hpa
      have e2 : ∑ i ∈ Finset.Ico 1 m, dd (m - i) * (α (j - m + i) + β (j - m + i) * p.coeff 0)
          = ∑ i ∈ Finset.Ico 1 m, dd (m - i) * α (j - m + i)
            + (∑ i ∈ Finset.Ico 1 m, dd (m - i) * β (j - m + i)) * p.coeff 0 := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e2] at hpa
      linarith

theorem solution (m : ℕ) (γ : ℕ → ℝ) (j : ℕ) (hmj : m ≤ j) (hj : j ≤ 2 * m - 1) :
    ∃ a b : ℝ, ∀ p : ℝ[X], p.Monic → p.natDegree = m →
      (∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → newtonSum p i = γ i) →
        newtonSum p j = a + b * p.coeff 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, 0, fun p _ hdeg _ => ?_⟩
    have : j = 0 := by omega
    subst this
    rw [spu_s0 0 p hdeg]; simp
  · obtain ⟨a, b, _, h⟩ := spu_affine_all m γ hm j hj
    exact ⟨a, b, fun p hp hdeg hγ => h p ⟨hp, hdeg, hγ⟩⟩
