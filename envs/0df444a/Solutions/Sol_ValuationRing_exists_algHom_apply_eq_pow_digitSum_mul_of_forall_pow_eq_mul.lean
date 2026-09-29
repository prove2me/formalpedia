-- Prove2me | solution 1 for ValuationRing.exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b4eb6b1b-32f6-58a7-8478-625776d1a1d2

import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul

universe u v

namespace RaynaudCoordSol

open scoped Fin.NatCast

section Digits

variable {r : ℕ} [NeZero r] (n : Fin r → ℕ) (p : ℕ)

private def E (i : Fin r) : ℕ → ℕ
  | 0 => 0
  | k + 1 => p * E i k + n (i + (k : Fin r))

private theorem E_succ (i : Fin r) (k : ℕ) : E n p i (k + 1) = p * E n p i k + n (i + (k : Fin r)) := rfl

private theorem E_succ_left (i : Fin r) : ∀ k : ℕ, E n p i (k + 1) = n i * p ^ k + E n p (i + 1) k
  | 0 => by simp [E]
  | k + 1 => by
      rw [E_succ n p i (k + 1), E_succ_left i k, E_succ n p (i + 1) k]
      have hidx : i + ((k + 1 : ℕ) : Fin r) = i + 1 + (k : Fin r) := by
        rw [Nat.cast_succ, add_comm (k : Fin r) 1, ← add_assoc]
      rw [hidx]
      ring

private theorem E_eq_sum_range (i : Fin r) :
    ∀ k : ℕ, E n p i k = ∑ j ∈ Finset.range k, n (i + (j : Fin r)) * p ^ (k - 1 - j)
  | 0 => by simp [E]
  | k + 1 => by
      rw [E_succ n p i k, E_eq_sum_range i k, Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < k := Finset.mem_range.mp hj
        have hexp : k + 1 - 1 - j = k - 1 - j + 1 := by omega
        rw [hexp, pow_succ]
        ring
      · simp

private theorem E_eq_sum (i : Fin r) : E n p i r = ∑ j : Fin r, n (i + j) * p ^ (r - 1 - (j : ℕ)) := by
  rw [E_eq_sum_range n p i r, Finset.sum_range]
  simp only [Fin.cast_val_eq_self]

private theorem E_shift (i : Fin r) : p * E n p i r + n i = E n p (i + 1) r + n i * p ^ r := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne r)
  have hidx : i + 1 + ((r' : ℕ) : Fin (r' + 1)) = i := by
    rw [add_assoc, add_comm (1 : Fin (r' + 1)), ← Nat.cast_succ, Fin.natCast_self, add_zero]
  rw [E_succ_left n p i r', E_succ n p (i + 1) r', hidx]
  ring

end Digits

section Powers

variable {S : Type v} [CommRing S] {r : ℕ} [NeZero r] (d : Fin r → S) (p : ℕ)

private def B (i : Fin r) : ℕ → S
  | 0 => 1
  | k + 1 => B i k ^ p * d (i + (k : Fin r))

private theorem B_succ (i : Fin r) (k : ℕ) : B d p i (k + 1) = B d p i k ^ p * d (i + (k : Fin r)) := rfl

private theorem pow_pow_eq (x : Fin r → S) (hx : ∀ i, x i ^ p = d i * x (i + 1)) (i : Fin r) :
    ∀ k : ℕ, x i ^ p ^ k = B d p i k * x (i + (k : Fin r))
  | 0 => by simp [B]
  | k + 1 => by
      rw [pow_succ, pow_mul, pow_pow_eq x hx i k, mul_pow, hx, B_succ, Nat.cast_succ, ← add_assoc]
      ring

private theorem pow_cycle (x : Fin r → S) (hx : ∀ i, x i ^ p = d i * x (i + 1)) (i : Fin r) :
    x i ^ p ^ r = B d p i r * x i := by
  have h := pow_pow_eq d p x hx i r
  rwa [Fin.natCast_self, add_zero] at h

private theorem pow_cycle_of_pow_eq_succ (c : Fin r → S) (hc : ∀ i, c i ^ p = c (i + 1)) (i : Fin r) :
    c i ^ p ^ r = c i := by
  have key : ∀ k : ℕ, c i ^ p ^ k = c (i + (k : Fin r)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hc, Nat.cast_succ, add_assoc]
  have h := key r
  rwa [Fin.natCast_self, add_zero] at h

private theorem associated_B (P : S) (n : Fin r → ℕ) (hd : ∀ i, Associated (d i) (P ^ n i)) (i : Fin r) :
    ∀ k : ℕ, Associated (B d p i k) (P ^ E n p i k)
  | 0 => by simp [B, E]
  | k + 1 => by
      rw [B_succ, E_succ, pow_add, pow_mul']
      exact ((associated_B P n hd i k).pow_pow).mul_mul (hd _)

end Powers

section Zero

variable {S : Type v} [CommRing S] [IsDomain S] {r : ℕ} [NeZero r]

private theorem all_zero (d : Fin r → S) {p : ℕ} (hp : p ≠ 0) (x : Fin r → S)
    (hx : ∀ i, x i ^ p = d i * x (i + 1)) {i₀ : Fin r} (h0 : x i₀ = 0) : ∀ i, x i = 0 := by
  have back : ∀ k : ℕ, x (i₀ - (k : Fin r)) = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
        have e : i₀ - ((k + 1 : ℕ) : Fin r) + 1 = i₀ - (k : Fin r) := by
          rw [Nat.cast_succ, sub_add_eq_sub_sub, sub_add_cancel]
        have h := hx (i₀ - ((k + 1 : ℕ) : Fin r))
        rw [e, ih, mul_zero] at h
        exact (pow_eq_zero_iff hp).mp h
  intro i
  have h := back ((i₀ - i : Fin r) : ℕ)
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at h

end Zero

section VR

variable {S : Type v} [CommRing S] [IsDomain S] [ValuationRing S]

private theorem associated_of_pow_associated_pow {a b : S} {N : ℕ} (hN : N ≠ 0)
    (h : Associated (a ^ N) (b ^ N)) : Associated a b := by
  have key : ∀ {a b : S} (c : S), a * c = b → Associated (a ^ N) (b ^ N) → Associated a b := by
    intro a b c hc h
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_mul] at hc
      subst hc
      exact Associated.refl 0
    · have h1 : Associated (a ^ N * 1) (a ^ N * c ^ N) := by rwa [mul_one, ← mul_pow, hc]
      have hcu : IsUnit c :=
        (isUnit_pow_iff hN).mp
          (associated_one_iff_isUnit.mp (h1.of_mul_left (Associated.refl _) (pow_ne_zero N ha)).symm)
      rw [← hc]
      exact associated_mul_unit_right a c hcu
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
  · exact key c hc h
  · exact (key c hc h.symm).symm

private theorem exists_mul_of_pow_eq {a b : S} {N : ℕ} (hN : N ≠ 0) (ha : a ≠ 0) (h : b ^ N = a ^ N) :
    ∃ t : S, t ^ N = 1 ∧ b = t * a := by
  have hassoc : Associated a b :=
    associated_of_pow_associated_pow hN ⟨1, by rw [Units.val_one, mul_one]; exact h.symm⟩
  obtain ⟨u, hu⟩ := hassoc
  refine ⟨u, ?_, by rw [← hu, mul_comm]⟩
  have h2 : a ^ N * (u : S) ^ N = a ^ N * 1 := by rw [mul_one, ← mul_pow, hu, h]
  exact mul_left_cancel₀ (pow_ne_zero N ha) h2

end VR

section PrincipalUnits

variable {S : Type v} [CommRing S] [IsLocalRing S]

private theorem pow_sub_one_mem {c : S} (hc : c - 1 ∈ IsLocalRing.maximalIdeal S) (k : ℕ) :
    c ^ k - 1 ∈ IsLocalRing.maximalIdeal S := by
  rw [← mul_geom_sum c k]
  exact Ideal.mul_mem_right _ _ hc

private theorem eq_one_of_pow_eq_one {c : S} (hc : c - 1 ∈ IsLocalRing.maximalIdeal S) {N : ℕ}
    (hN : (N : S) + 1 ∈ IsLocalRing.maximalIdeal S) (h : c ^ N = 1) : c = 1 := by
  have hgm : (∑ k ∈ Finset.range N, c ^ k) + 1 ∈ IsLocalRing.maximalIdeal S := by
    have e : (∑ k ∈ Finset.range N, c ^ k) + 1 = (∑ k ∈ Finset.range N, (c ^ k - 1)) + ((N : S) + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      ring
    rw [e]
    exact add_mem (sum_mem fun k _ => pow_sub_one_mem hc k) hN
  have hgu : IsUnit (∑ k ∈ Finset.range N, c ^ k) := by
    by_contra hnu
    have hg : (∑ k ∈ Finset.range N, c ^ k) ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have h2 := sub_mem hgm hg
      rwa [add_sub_cancel_left] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h0 : (c - 1) * ∑ k ∈ Finset.range N, c ^ k = 0 := by rw [mul_geom_sum, h, sub_self]
  exact sub_eq_zero.mp (hgu.mul_left_eq_zero.mp h0)

end PrincipalUnits

end RaynaudCoordSol

open RaynaudCoordSol in
theorem solution
    {R : Type u} [CommRing R] {p : ℕ} (hunif : Irreducible (p : R))
    {S : Type v} [CommRing S] [IsDomain S] [ValuationRing S] [Algebra R S]
    (hpS : algebraMap R S p ∈ IsLocalRing.maximalIdeal S) (hp0 : algebraMap R S p ≠ 0)
    (σ : S →ₐ[R] S) (hσ : ∀ y : S, σ y - y ∈ IsLocalRing.maximalIdeal S)
    {r : ℕ} [NeZero r] (δ : Fin r → R) (hδ : ∀ i, δ i ∣ (p : R))
    (x : Fin r → S) (hx : ∀ i, x i ^ p = algebraMap R S (δ i) * x (i + 1))
    (π' : S) (hπ' : π' ^ (p ^ r - 1) = algebraMap R S p) :
    ∃ n : Fin r → ℕ, (∀ i, n i ≤ 1) ∧ (∀ i, Associated (δ i) ((p : R) ^ n i)) ∧
      ∃ t : S, t ^ (p ^ r - 1) = 1 ∧ σ π' = t * π' ∧
        ∀ i, σ (x i) = t ^ (∑ j : Fin r, n (i + j) * p ^ (r - 1 - (j : ℕ))) * x i := by
  classical

  have hp0' : p ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hunif
    exact not_irreducible_zero hunif
  have hp1 : p ≠ 1 := by
    rintro rfl
    exact hunif.not_isUnit (by simp)
  have hp2 : 2 ≤ p := by omega
  have hr0 : r ≠ 0 := NeZero.ne r
  have hq : p ≤ p ^ r :=
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hr0)
  have hN0 : p ^ r - 1 ≠ 0 := by omega

  obtain ⟨P, hP⟩ : ∃ P : S, algebraMap R S (p : R) = P := ⟨_, rfl⟩
  rw [hP] at hpS hp0 hπ'
  have hσP : σ P = P := by rw [← hP]; exact σ.commutes _
  have hPnat : (p : S) = P := by rw [← hP, map_natCast]

  obtain ⟨n, hn⟩ : ∃ n : Fin r → ℕ, ∀ i, n i = if IsUnit (δ i) then 0 else 1 := ⟨_, fun _ => rfl⟩
  have hn1 : ∀ i, n i ≤ 1 := fun i => by rw [hn i]; split_ifs <;> simp
  have hnδ : ∀ i, Associated (δ i) ((p : R) ^ n i) := by
    intro i
    rw [hn i]
    split_ifs with h
    · rw [pow_zero]; exact associated_one_iff_isUnit.mpr h
    · rw [pow_one]
      obtain ⟨c, hc⟩ := hδ i
      rcases hunif.isUnit_or_isUnit hc with hu | hu
      · exact absurd hu h
      · exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  have hd : ∀ i, Associated (algebraMap R S (δ i)) (P ^ n i) := fun i => by
    have h := (hnδ i).map (algebraMap R S)
    rwa [map_pow, hP] at h

  have hπ0 : π' ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hπ'
    exact hp0 hπ'.symm
  have hσπN : σ π' ^ (p ^ r - 1) = π' ^ (p ^ r - 1) := by rw [← map_pow, hπ', hσP]
  obtain ⟨t, htN, hσπ⟩ := exists_mul_of_pow_eq hN0 hπ0 hσπN
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at htN
    exact zero_ne_one htN
  refine ⟨n, hn1, hnδ, t, htN, hσπ, ?_⟩
  by_cases hz : ∃ i, x i = 0
  ·
    obtain ⟨i₀, hi₀⟩ := hz
    have hall := all_zero (fun i => algebraMap R S (δ i)) hp0' x hx hi₀
    intro i
    rw [hall i, mul_zero, map_zero]
  · have hz' : ∀ i, x i ≠ 0 := fun i h => hz ⟨i, h⟩

    have hB : ∀ i, x i ^ (p ^ r - 1) = B (fun i => algebraMap R S (δ i)) p i r := by
      intro i
      have h := pow_cycle (fun i => algebraMap R S (δ i)) p x hx i
      have e : p ^ r = p ^ r - 1 + 1 := by omega
      rw [e, pow_succ] at h
      exact mul_right_cancel₀ (hz' i) h

    have hxa : ∀ i, ∃ w : Sˣ, π' ^ E n p i r * w = x i := by
      intro i
      refine associated_of_pow_associated_pow hN0 ?_
      rw [← pow_mul, mul_comm (E n p i r), pow_mul, hπ', hB i]
      exact (associated_B _ p P n hd i r).symm
    choose u hu using hxa

    have hcdef : ∀ i, ∃ c : S, c - 1 ∈ IsLocalRing.maximalIdeal S ∧ σ (u i) = c * u i := fun i =>
      ⟨σ (u i) * ↑(u i)⁻¹,
        by
          rw [show σ (u i) * ↑(u i)⁻¹ - 1 = (σ (u i) - u i) * ↑(u i)⁻¹ by rw [sub_mul, Units.mul_inv]]
          exact Ideal.mul_mem_right _ _ (hσ _),
        by rw [mul_assoc, Units.inv_mul, mul_one]⟩
    choose c hc1 hcu using hcdef
    have hσx : ∀ i, σ (x i) = c i * t ^ E n p i r * x i := by
      intro i
      rw [← hu i, map_mul, map_pow, hσπ, hcu i, mul_pow]
      ring

    have htpr : t ^ p ^ r = t := by
      have e : p ^ r = p ^ r - 1 + 1 := by omega
      rw [e, pow_succ, htN, one_mul]
    have hshift : ∀ i, (t ^ E n p i r) ^ p = t ^ E n p (i + 1) r := by
      intro i
      have h : t ^ (p * E n p i r + n i) = t ^ (E n p (i + 1) r + n i * p ^ r) := by rw [E_shift n p i]
      rw [pow_add, pow_add, pow_mul' t (n i) (p ^ r), htpr] at h
      rw [← pow_mul, mul_comm (E n p i r) p]
      exact mul_right_cancel₀ (pow_ne_zero _ ht0) h

    have hcp : ∀ i, c i ^ p = c (i + 1) := by
      intro i
      have h1 := congrArg σ (hx i)
      rw [map_pow, map_mul, AlgHom.commutes, hσx i, hσx (i + 1), mul_pow, mul_pow, hshift i, hx i] at h1
      have hne : t ^ E n p (i + 1) r * (algebraMap R S (δ i) * x (i + 1)) ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ ht0) ?_
        rw [← hx i]
        exact pow_ne_zero _ (hz' i)
      apply mul_right_cancel₀ hne
      calc c i ^ p * (t ^ E n p (i + 1) r * (algebraMap R S (δ i) * x (i + 1)))
          = c i ^ p * t ^ E n p (i + 1) r * (algebraMap R S (δ i) * x (i + 1)) := by ring
        _ = algebraMap R S (δ i) * (c (i + 1) * t ^ E n p (i + 1) r * x (i + 1)) := h1
        _ = c (i + 1) * (t ^ E n p (i + 1) r * (algebraMap R S (δ i) * x (i + 1))) := by ring

    have hNS : ((p ^ r - 1 : ℕ) : S) + 1 = P ^ r := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel (show 1 ≤ p ^ r by omega), Nat.cast_pow, hPnat]
    have hN1 : ((p ^ r - 1 : ℕ) : S) + 1 ∈ IsLocalRing.maximalIdeal S := by
      rw [hNS]
      exact Ideal.pow_mem_of_mem _ hpS r (Nat.pos_of_ne_zero hr0)
    have hcN : ∀ i, c i ^ (p ^ r - 1) = 1 := by
      intro i
      have hc0 : c i ≠ 0 := by
        intro h0
        have h2 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
          have h3 := hc1 i
          rwa [h0, zero_sub, Ideal.neg_mem_iff] at h3
        exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
      have h := pow_cycle_of_pow_eq_succ p c hcp i
      have e : p ^ r = p ^ r - 1 + 1 := by omega
      rw [e, pow_succ] at h
      exact mul_right_cancel₀ hc0 (h.trans (one_mul _).symm)

    intro i
    rw [hσx i, eq_one_of_pow_eq_one (hc1 i) hN1 (hcN i), one_mul, E_eq_sum n p i]

end S_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
end P2MW
export P2MW.S_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul (solution)
