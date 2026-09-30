-- Prove2me | solution 1 for WeierstrassEllipticZeta.period_image_multiplicity_le_of_wp_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T01:51:03.871972+00:00
-- url     : https://prove2.me/submissions/8bb7bce3-0fef-4806-ac16-b7e314adb446

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Tactic

noncomputable section
open WeierstrassEllipticZeta
open scoped Classical

private lemma wp_equal_mod_sign (L : PeriodPair) (D : EllipticSigmaData L)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (heq : L.weierstrassP z = L.weierstrassP v) :
    L.lattice.mkQ z = L.lattice.mkQ v ∨
      L.lattice.mkQ z = -L.lattice.mkQ v := by
  have hzero (a : ℂ) (ha : D.sigma a = 0) : a ∈ L.lattice := by
    by_contra hn
    exact D.ne_zero a hn ha
  have h := D.addition z v hz hv
  rw [heq, sub_self, zero_mul, zero_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · right
    rw [← map_neg, Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq L.lattice).mpr
    simpa only [sub_neg_eq_add] using hzero _ h
  · left
    exact (Submodule.Quotient.eq L.lattice).mpr (hzero _ h)

private lemma period_card_le_twice_wp_card (L : PeriodPair) (D : EllipticSigmaData L)
    (Y : Finset ℂ) :
    (L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤
      2 * ((Y.filter (fun z => z ∉ L.lattice)).image L.weierstrassP).card + 1 := by
  classical
  let V := (Y.filter (fun z => z ∉ L.lattice)).image L.weierstrassP
  have hrep : ∀ a : V, ∃ z : ℂ, z ∈ Y ∧ z ∉ L.lattice ∧ L.weierstrassP z = a.val := by
    intro a
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp a.property
    exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2, heq⟩
  choose r hr using hrep
  let T : Finset (ℂ ⧸ L.lattice) :=
    Finset.univ.biUnion (fun a : V => {L.lattice.mkQ (r a), -L.lattice.mkQ (r a)})
  have hT : T.card ≤ 2 * V.card := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset V)
      (fun a : V => {L.lattice.mkQ (r a), -L.lattice.mkQ (r a)}) 2
      (fun a _ => by simpa using
        Finset.card_insert_le (L.lattice.mkQ (r a)) {-L.lattice.mkQ (r a)})
    simpa only [Finset.card_univ, Fintype.card_coe, mul_comm] using h
  have hsub : Y.image L.lattice.mkQ ⊆ insert 0 T := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    by_cases hzl : z ∈ L.lattice
    · have hz0 : L.lattice.mkQ z = 0 := by
        change (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) = Submodule.Quotient.mk 0
        exact (Submodule.Quotient.eq L.lattice).mpr (by simpa using hzl)
      simp only [hz0, Finset.mem_insert, true_or]
    · let a : V := ⟨L.weierstrassP z,
        Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hzl⟩, rfl⟩⟩
      have hsign := wp_equal_mod_sign L D z (r a) hzl (hr a).2.1 (hr a).2.2.symm
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_univ _, ?_⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hsign
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  exact hcard.trans (Nat.add_le_add_right hT 1)

/-- A polynomial with repeated roots at the regular wp-values bounds period classes. -/
theorem solution
    (L : PeriodPair) (D : EllipticSigmaData L) (Y : Finset ℂ)
    (w : ℕ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hdiv : ∀ z ∈ Y, z ∉ L.lattice →
      (Polynomial.X - Polynomial.C (L.weierstrassP z)) ^ w ∣ p) :
    w * (L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤ 2 * p.natDegree + w := by
  classical
  let V := (Y.filter (fun z => z ∉ L.lattice)).image L.weierstrassP
  let M : Polynomial ℂ := ∏ a ∈ V, (Polynomial.X - Polynomial.C a) ^ w
  have hdegree : M.natDegree = w * V.card := by
    change (∏ a ∈ V, (Polynomial.X - Polynomial.C a) ^ w).natDegree = _
    rw [Polynomial.natDegree_prod_of_monic V _
      (fun a _ => (Polynomial.monic_X_sub_C a).pow w)]
    simp [mul_comm]
  have hMp : M ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact (Polynomial.pairwise_coprime_X_sub_C (s := fun x : ℂ => x)
        Function.injective_id hab).pow
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact hdiv z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  have hdeg : w * V.card ≤ p.natDegree := by
    rw [← hdegree]
    exact Polynomial.natDegree_le_of_dvd hMp hp
  calc
    w * (L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤ w * (2 * V.card + 1) :=
      Nat.mul_le_mul_left w (period_card_le_twice_wp_card L D Y)
    _ = 2 * (w * V.card) + w := by ring
    _ ≤ 2 * p.natDegree + w := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdeg) w
