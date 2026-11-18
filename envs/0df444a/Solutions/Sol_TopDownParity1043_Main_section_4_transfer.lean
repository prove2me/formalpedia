-- Prove2me | solution 1 for TopDownParity1043.Main.section_4_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:07:17.473057+00:00
-- url     : https://prove2.me/submissions/8c5a7c84-9b6f-4762-993d-52c702188b9e

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets

set_option autoImplicit false
open scoped NNReal ENNReal
open TopDownParity1043.Main

private noncomputable def mass {V : Type} [DecidableEq V]
    (p : ℝ) (U : Finset V) (A : Set (Finset V)) : ℝ :=
  by
    classical
    exact ∑ R ∈ U.powerset,
      if R ∈ A then p ^ R.card * (1 - p) ^ (U.card - R.card) else 0

private theorem mass_insert {V : Type} [DecidableEq V]
    (p : ℝ) (s : Finset V) (a : V) (ha : a ∉ s) (A : Set (Finset V)) :
    mass p (insert a s) A =
      (1 - p) * mass p s A + p * mass p s {R | insert a R ∈ A} := by
  classical
  simp only [mass, Finset.powerset_insert]
  rw [Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.card_insert_of_notMem ha]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := Finset.notMem_of_mem_powerset_of_notMem hR ha
        split <;> rename_i hA
        · have hcard : R.card ≤ s.card :=
            Finset.card_le_card (Finset.mem_powerset.mp hR)
          have he : s.card + 1 - R.card = (s.card - R.card) + 1 := by omega
          rw [he, pow_succ]
          ring
        · simp [hA]
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := Finset.notMem_of_mem_powerset_of_notMem hR ha
        rw [Finset.card_insert_of_notMem haR]
        split <;> rename_i hA
        · have hcard : R.card ≤ s.card :=
            Finset.card_le_card (Finset.mem_powerset.mp hR)
          have he : s.card + 1 - (R.card + 1) = s.card - R.card := by omega
          simp [hA, he, pow_succ]
          ring
        · simp [hA]
    · intro R hR T hT heq
      apply Finset.ext
      intro x
      have haR : a ∉ R := Finset.notMem_of_mem_powerset_of_notMem hR ha
      have haT : a ∉ T := Finset.notMem_of_mem_powerset_of_notMem hT ha
      by_cases hx : x = a
      · subst x
        simp [haR, haT]
      · have hxmem := Finset.ext_iff.mp heq x
        simpa [hx] using hxmem
  · apply Finset.disjoint_left.mpr
    intro R hR hRi
    rw [Finset.mem_image] at hRi
    obtain ⟨T, hT, rfl⟩ := hRi
    exact (Finset.notMem_of_mem_powerset_of_notMem hR ha) (Finset.mem_insert_self a T)

private theorem mass_univ {V : Type} [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset V) :
    mass p U Set.univ = 1 := by
  classical
  induction U using Finset.induction with
  | empty => simp [mass]
  | @insert a s ha ih =>
      rw [mass_insert p s a ha Set.univ]
      have hfamily : {R : Finset V | insert a R ∈ (Set.univ : Set (Finset V))} = Set.univ := by
        ext R
        simp
      rw [hfamily, ih]
      ring

private theorem mass_nonneg {V : Type} [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset V) (A : Set (Finset V)) :
    0 ≤ mass p U A := by
  classical
  simp only [mass]
  positivity

private theorem mass_le_one {V : Type} [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset V) (A : Set (Finset V)) :
    mass p U A ≤ 1 := by
  classical
  rw [← mass_univ p hp0 hp1 U]
  simp only [mass]
  apply Finset.sum_le_sum
  intro R hR
  by_cases hA : R ∈ A
  · simp [hA]
  · simp [hA]
    positivity

private theorem normalized_transfer (r t : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((3 / 4 : ℝ) + (1 / 4 : ℝ) * t) ^ (5 * r) ≤
      (1 - r) + r * t ^ (5 * r) := by
  have hc0 : 0 ≤ 5 * r := by positivity
  have hc1 : 5 * r ≤ 1 := by linarith
  have ht_pow : t ≤ t ^ (5 * r) :=
    Real.self_le_rpow_of_le_one ht0 ht1 hc1
  let s : ℝ := -(1 / 4 : ℝ) * (1 - t)
  have hs : -1 ≤ s := by
    dsimp [s]
    nlinarith
  have hbase : 1 + s = (3 / 4 : ℝ) + (1 / 4 : ℝ) * t := by
    dsimp [s]
    ring
  have hbern := rpow_one_add_le_one_add_mul_self hs hc0 hc1
  rw [hbase] at hbern
  have hmid :
      1 + (5 * r) * s ≤ (1 - r) + r * t ^ (5 * r) := by
    dsimp [s]
    nlinarith
  exact hbern.trans hmid

private theorem scalar_transfer (r a b : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hba : b ≤ a) :
    ((3 / 4 : ℝ) * a + (1 / 4 : ℝ) * b) ^ (5 * r) ≤
      (1 - r) * a ^ (5 * r) + r * b ^ (5 * r) := by
  by_cases ha : a = 0
  · have hb : b = 0 := le_antisymm (ha ▸ hba) hb0
    simp [ha, hb]
    nlinarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    let t : ℝ := b / a
    have ht0 : 0 ≤ t := div_nonneg hb0 ha0
    have ht1 : t ≤ 1 := (div_le_one ha_pos).mpr hba
    have hbase0 : 0 ≤ (3 / 4 : ℝ) + (1 / 4 : ℝ) * t := by positivity
    have hnorm := normalized_transfer r t hr0 hr ht0 ht1
    have hmix : (3 / 4 : ℝ) * a + (1 / 4 : ℝ) * b =
        a * ((3 / 4 : ℝ) + (1 / 4 : ℝ) * t) := by
      dsimp [t]
      field_simp [ha]
    have hbmul : b = a * t := by
      dsimp [t]
      field_simp [ha]
    calc
      ((3 / 4 : ℝ) * a + (1 / 4 : ℝ) * b) ^ (5 * r) =
          (a * ((3 / 4 : ℝ) + (1 / 4 : ℝ) * t)) ^ (5 * r) := by rw [hmix]
      _ = a ^ (5 * r) * ((3 / 4 : ℝ) + (1 / 4 : ℝ) * t) ^ (5 * r) :=
        Real.mul_rpow ha0 hbase0
      _ ≤ a ^ (5 * r) * ((1 - r) + r * t ^ (5 * r)) :=
        mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg ha0 _)
      _ = (1 - r) * a ^ (5 * r) + r * b ^ (5 * r) := by
        rw [hbmul, Real.mul_rpow ha0 ht0]
        ring

private theorem mass_mono {V : Type} [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset V)
    (A B : Set (Finset V)) (hAB : A ⊆ B) : mass p U A ≤ mass p U B := by
  classical
  apply Finset.sum_le_sum
  intro R hR
  by_cases ha : R ∈ A
  · simp [ha, hAB ha]
  · simp [ha]
    positivity

private theorem mass_transfer {V : Type} [DecidableEq V]
    (U : Finset V) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 1 / 20)
    (A : Set (Finset V)) (hd : DownwardClosed A) :
    (mass (1 / 4) U A) ^ (5 * r) ≤ mass r U A := by
  classical
  induction U using Finset.induction generalizing A with
  | empty =>
      by_cases he : ∅ ∈ A <;> simp [mass, he, Real.zero_rpow (by positivity : 5 * r ≠ 0)]
  | @insert a s ha ih =>
      let B : Set (Finset V) := {R | insert a R ∈ A}
      have hdB : DownwardClosed B := by
        intro R hR T hTR
        exact hd (insert a R) hR (insert a T) (Finset.insert_subset_insert a hTR)
      have hBA : B ⊆ A := by
        intro R hR
        exact hd (insert a R) hR R (Finset.subset_insert a R)
      have hia := ih A hd
      have hib := ih B hdB
      rw [mass_insert _ s a ha, mass_insert _ s a ha]
      change ((1 - 1 / 4 : ℝ) * mass (1 / 4) s A +
          (1 / 4 : ℝ) * mass (1 / 4) s B) ^ (5 * r) ≤
        (1 - r) * mass r s A + r * mass r s B
      norm_num only [show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num]
      apply le_trans (scalar_transfer r (mass (1 / 4) s A) (mass (1 / 4) s B)
        hr0.le hr (mass_nonneg _ (by norm_num) (by norm_num) _ _)
        (mass_le_one _ (by norm_num) (by norm_num) _ _)
        (mass_nonneg _ (by norm_num) (by norm_num) _ _)
        (mass_mono _ (by norm_num) (by norm_num) s B A hBA))
      exact add_le_add
        (mul_le_mul_of_nonneg_left hia (by linarith))
        (mul_le_mul_of_nonneg_left hib hr0.le)

private theorem setProb_eq_mass (V : Type) [Fintype V] [DecidableEq V]
    (p : Bias) (A : Set (Finset V)) :
    setProb p (fun R => R ∈ A) = mass (p : ℝ) Finset.univ A := by
  classical
  have hall : (Finset.univ : Finset (Finset V)) =
      (Finset.univ : Finset V).powerset := by
    ext R
    simp
  simp only [setProb, mass, setWeight]
  rw [← hall]
  simp

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (A : Set (Finset V)) (hA : A.Nonempty) (hdown : DownwardClosed A)
    (r : Bias) (hr : (r : ℝ) ≤ 1 / 20) :
    (setProb quarterBias (fun S : Finset V => S ∈ A)) ^ (5 * (r : ℝ)) ≤
      setProb r (fun R : Finset V => R ∈ A) := by
  classical
  by_cases hr0 : (r : ℝ) = 0
  · have he : (∅ : Finset V) ∈ A := by
      obtain ⟨R, hR⟩ := hA
      exact hdown R hR ∅ (Finset.empty_subset R)
    have hm : setProb r (fun R : Finset V => R ∈ A) = 1 := by
      simp only [setProb, setWeight, hr0]
      rw [Finset.sum_eq_single ∅]
      · simp [he]
      · intro R hR hne
        have hc : R.card ≠ 0 := by simpa using hne
        simp [zero_pow hc]
      · simp
    simp [hr0, hm]
  · rw [setProb_eq_mass, setProb_eq_mass]
    exact mass_transfer Finset.univ (r : ℝ)
      (lt_of_le_of_ne r.property.1 (Ne.symm hr0)) hr A hdown
