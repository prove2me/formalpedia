-- Prove2me | solution 1 for ShorAlgorithms.Reduction.card_twoAdic_le_half
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:27:27.302974+00:00
-- url     : https://prove2.me/submissions/9a1f1c08-5372-4de7-8a59-e99a0a453454

import Mathlib
open scoped BigOperators
namespace AShorCard
private theorem valuation_of_not_half {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r)
    (hhalf : ¬ d ∣ r/2) : padicValNat 2 d = padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hr
  have hk0 : k ≠ 0 := by intro h; simp [h] at hr
  have hk : ¬ 2 ∣ k := by
    rintro ⟨l,rfl⟩
    apply hhalf
    refine ⟨l,?_⟩
    rw [show d*(2*l)=(d*l)*2 by ring]
    omega
  rw [padicValNat.mul hd0 hk0,padicValNat.eq_zero_of_not_dvd hk,add_zero]


private theorem valuation_le_dvd {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r) :
    padicValNat 2 d ≤ padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  rw [padicValNat.mul (left_ne_zero_of_mul hr) (right_ne_zero_of_mul hr)]
  omega

theorem cyclic_half (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (hN : Even (Fintype.card G)) (e : ℕ) :
    2 * Nat.card {u : G // padicValNat 2 (orderOf u) = e} ≤ Fintype.card G := by
  classical
  let N := Fintype.card G
  have hNp : 0 < N := Fintype.card_pos
  have hN2 : N/2*2=N := Nat.div_mul_cancel hN.two_dvd
  have hhpos : 0 < N/2 := by omega
  let K : Subgroup G := (powMonoidHom (N/2) : G →* G).ker
  have hKd : N/2 ∣ N := ⟨2,hN2.symm⟩
  have hKcard : Fintype.card K = N/2 := by
    have h := IsCyclic.card_powMonoidHom_ker G (N/2)
    simp only [Nat.card_eq_fintype_card] at h
    change Fintype.card K = N.gcd (N/2) at h
    rw [Nat.gcd_eq_right hKd] at h
    exact h
  have hKmem (u : G) : u ∈ K ↔ orderOf u ∣ N/2 := by
    change u^(N/2)=1 ↔ orderOf u ∣ N/2
    exact orderOf_dvd_iff_pow_eq_one.symm
  have hval : padicValNat 2 N = padicValNat 2 (N/2)+1 := by
    rw [←hN2,padicValNat.mul hhpos.ne' (by decide)]
    norm_num
  rw [Nat.card_eq_fintype_card]
  by_cases he : e = padicValNat 2 N
  · have hsub : (fun u : G => padicValNat 2 (orderOf u) = e) ≤ (fun u => u ∉ K) := by
      intro u hu hmem
      have hv := valuation_le_dvd hhpos.ne' ((hKmem u).mp hmem)
      rw [hu,he] at hv
      omega
    have hc := Fintype.card_subtype_mono _ _ hsub
    rw [Fintype.card_subtype_compl] at hc
    change Fintype.card {u : G // padicValNat 2 (orderOf u) = e} ≤ N - Fintype.card K at hc
    rw [hKcard] at hc
    omega
  · have hsub : (fun u : G => padicValNat 2 (orderOf u) = e) ≤ (fun u => u ∈ K) := by
      intro u hu
      rw [hKmem]
      by_contra hno
      have hv := valuation_of_not_half hNp.ne' (orderOf_dvd_card (x := u)) hno
      exact he (hu.symm.trans hv)
    have hc := Fintype.card_subtype_mono _ _ hsub
    change Fintype.card {u : G // padicValNat 2 (orderOf u) = e} ≤ Fintype.card K at hc
    rw [hKcard] at hc
    omega
end AShorCard

theorem solution (p α e : ℕ) (hp : p.Prime) (hodd : Odd p) (hα : 1 ≤ α) :
    2 * Nat.card {u : (ZMod (p ^ α))ˣ // padicValNat 2 (orderOf u) = e}
      ≤ Nat.totient (p ^ α) := by
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat dvd_rfl
  have hplt : 2 < p := by have := hp.two_le; omega
  have hpow : 2 < p^α := hplt.trans_le (by simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ p) hα)
  haveI : NeZero (p^α) := ⟨by omega⟩
  haveI : IsCyclic (ZMod (p^α))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 α
  have hc : Fintype.card (ZMod (p^α))ˣ = Nat.totient (p^α) := ZMod.card_units_eq_totient _
  have heven : Even (Fintype.card (ZMod (p^α))ˣ) := by rw [hc]; exact Nat.totient_even hpow
  simpa only [hc] using AShorCard.cyclic_half (ZMod (p^α))ˣ heven e
