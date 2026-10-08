-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_source_order_one_exponent_large
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T17:17:09.056078+00:00
-- url     : https://prove2.me/submissions/27b66188-ad71-4260-857e-d268f3024066

-- Target: OddPerfectNumber.Kernel.sigma_source_order_one_exponent_large (d7dcfa98).
-- Round-13 repair of candidate 7340 (1 group: L66 TYPE MISMATCH, fully read).
-- Authoritative evidence: `.mp hdvd` produced `p ∣ p*?m + (2*e+1+p*S)`, proving the
-- pinned `Nat.dvd_add_iff_right` has shape `(h : k ∣ m) : k ∣ n ↔ k ∣ m + n`
-- (conclusion appends, not strips). Hence extraction needs `.mpr`, and the known
-- divisible block must come FIRST: reorder `hdvd` with `Nat.add_comm` so it reads
-- `p ∣ p*S + 2*e+1`, then `.mpr` yields `p ∣ 2*e+1`. `dvd_mul_left` variant (7342)
-- remains pending as the orientation cross-check; this candidate tests .mpr+reorder.
import Mathlib

theorem solution {p t e : Nat} (hp : p.Prime)
    (ht : t.Prime)
    (hpt : Not (Dvd.dvd p t))
    (hord : Dvd.dvd p (t - 1))
    (h : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (p - 1) / 2 <= e := by
  have hp2 : (2 : Nat) <= p := hp.two_le
  have hone : (1 : Nat) < p := by omega
  rcases hord with ⟨c, hc⟩
  have ht2 : (2 : Nat) <= t := ht.two_le
  have htdecomp : t = p * c + 1 := by omega
  have hone' : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hone
  have htmod : t % p = 1 := by
    rw [htdecomp]
    rw [show p * c + 1 = 1 + p * c by ring, Nat.add_mul_mod_self_left, hone']
  have hmod : ∀ i : Nat, t ^ i % p = 1 := by
    intro i
    induction i with
    | zero => exact hone'
    | succ i ih =>
        rw [pow_succ, Nat.mul_mod, ih, htmod]
        simp [hone']
  have hlen : (∑ _i ∈ Finset.range (2 * e + 1), (1 : Nat)) = 2 * e + 1 := by
    induction (2 * e + 1) with
    | zero => simp
    | succ n ih => simp [Finset.sum_range_succ, ih]
  have hdecomp :
      (∑ i ∈ Finset.range (2 * e + 1), t ^ i)
        = (2 * e + 1) + p * (∑ i ∈ Finset.range (2 * e + 1), t ^ i / p) := by
    calc (∑ i ∈ Finset.range (2 * e + 1), t ^ i)
        = ∑ i ∈ Finset.range (2 * e + 1), (1 + p * (t ^ i / p)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hdiv := Nat.mod_add_div (t ^ i) p
          rw [hmod i] at hdiv
          omega
      _ = (∑ _i ∈ Finset.range (2 * e + 1), (1 : Nat))
          + ∑ i ∈ Finset.range (2 * e + 1), p * (t ^ i / p) :=
          Finset.sum_add_distrib
      _ = (2 * e + 1) + p * (∑ i ∈ Finset.range (2 * e + 1), t ^ i / p) := by
          rw [hlen]
          congr 1
          exact (Finset.mul_sum _ _ _).symm
  rcases h with ⟨c', hc'⟩
  rw [hdecomp] at hc'
  have hmain : p ∣ 2 * e + 1 := by
    have hdvd : p ∣ (2 * e + 1 + p * (∑ i ∈ Finset.range (2 * e + 1), t ^ i / p)) := by
      rw [hc']
      exact dvd_mul_right p c'
    have hre : p ∣ (p * (∑ i ∈ Finset.range (2 * e + 1), t ^ i / p) + (2 * e + 1)) := by
      rwa [Nat.add_comm] at hdvd
    exact (Nat.dvd_add_iff_right (dvd_mul_right p _)).mpr hre
  have hpos21 : 0 < 2 * e + 1 := by omega
  have hple : p ≤ 2 * e + 1 := Nat.le_of_dvd hpos21 hmain
  have hsub : p - 1 ≤ 2 * e := by omega
  have hfloor : (p - 1) / 2 * 2 ≤ p - 1 := by omega
  have hchain : (p - 1) / 2 * 2 ≤ 2 * e := hfloor.trans hsub
  have hchain' : 2 * ((p - 1) / 2) ≤ 2 * e := by simpa [Nat.mul_comm] using hchain
  exact Nat.le_of_mul_le_mul_left hchain' (by omega)
