-- Prove2me | solution 1 for ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b47aeff7-fafa-59ce-ab87-8d9d92095ae2

import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff

namespace EsbLeGen

open IsLocalRing

section valuationSubring

variable {F : Type*} [Field F]

theorem one_lt_valuation_of_not_mem (O : ValuationSubring F) {z : F} (hz : z ∉ O) :
    1 < O.valuation z := by
  rw [← not_le, O.valuation_le_one_iff]; exact hz

theorem ne_zero_of_not_mem (O : ValuationSubring F) {z : F} (hz : z ∉ O) : z ≠ 0 := by
  rintro rfl; exact hz (zero_mem O)

theorem residue_mk_eq_zero_iff (O : ValuationSubring F) {x : F} (hx : x ∈ O) :
    residue O ⟨x, hx⟩ = 0 ↔ O.valuation x < 1 := by
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem residue_mk_eq_residue_mk_iff (O : ValuationSubring F) {x y : F} (hx : x ∈ O)
    (hy : y ∈ O) : residue O ⟨x, hx⟩ = residue O ⟨y, hy⟩ ↔ O.valuation (x - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub]
  exact residue_mk_eq_zero_iff O (sub_mem hx hy)

theorem valuation_eq_one_of_residue_ne_zero (O : ValuationSubring F) {x : F} (hx : x ∈ O)
    (h : residue O ⟨x, hx⟩ ≠ 0) : O.valuation x = 1 := by
  rcases O.valuation_lt_one_or_eq_one ⟨x, hx⟩ with h1 | h1
  · exact absurd ((residue_mk_eq_zero_iff O hx).mpr h1) h
  · exact h1

theorem inv_mem_of_one_le (O : ValuationSubring F) {u : F} (hu : 1 ≤ O.valuation u) :
    u⁻¹ ∈ O := by
  rw [← O.valuation_le_one_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ hu

theorem inv_sub_one (O : ValuationSubring F) {u : F} (h1 : O.valuation (u - 1) < 1) :
    O.valuation u = 1 ∧ u⁻¹ ∈ O ∧ O.valuation (u⁻¹ - 1) < 1 := by
  have hu : O.valuation u = 1 := by
    have : u = 1 + (u - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ h1
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact zero_ne_one hu
  refine ⟨hu, inv_mem_of_one_le O hu.ge, ?_⟩
  have : u⁻¹ - 1 = -(u⁻¹ * (u - 1)) := by
    rw [mul_sub, inv_mul_cancel₀ hu0, mul_one]; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hu, inv_one, one_mul]
  exact h1

theorem prod_sub_one (O : ValuationSubring F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ l ∈ s, f l ∈ O ∧ O.valuation (f l - 1) < 1) :
    (∏ l ∈ s, f l) ∈ O ∧ O.valuation (∏ l ∈ s, f l - 1) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp [one_mem], by simp⟩
  | @insert a s ha ih =>
    obtain ⟨hmem, hv⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    obtain ⟨hamem, hav⟩ := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    refine ⟨mul_mem hamem hmem, ?_⟩
    have : f a * ∏ l ∈ s, f l - 1 = f a * (∏ l ∈ s, f l - 1) + (f a - 1) := by ring
    rw [this]
    apply Valuation.map_add_lt _ _ hav
    rw [map_mul]
    calc O.valuation (f a) * O.valuation (∏ l ∈ s, f l - 1)
        ≤ 1 * O.valuation (∏ l ∈ s, f l - 1) := by
          gcongr; exact (O.valuation_le_one_iff _).mpr hamem
      _ < 1 := by rwa [one_mul]

theorem geom_mem (O : ValuationSubring F) {z : F} (hz : z ∈ O) (m : ℕ) :
    (∑ k ∈ Finset.range m, z ^ k) ∈ O :=
  sum_mem fun k _ => pow_mem hz k

theorem residue_geom (O : ValuationSubring F) {z : F} (hz : z ∈ O) (m : ℕ) :
    residue O ⟨∑ k ∈ Finset.range m, z ^ k, geom_mem O hz m⟩ =
      ∑ k ∈ Finset.range m, (residue O ⟨z, hz⟩) ^ k := by
  have : (⟨∑ k ∈ Finset.range m, z ^ k, geom_mem O hz m⟩ : O) =
      ∑ k ∈ Finset.range m, (⟨z, hz⟩ : O) ^ k := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [SubmonoidClass.coe_pow]
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_pow _ _ _

theorem valuation_geom_sub_one_lt (O : ValuationSubring F) {z : F} (hz : z ∈ O)
    (hv : O.valuation z < 1) {m : ℕ} (hm : 1 ≤ m) :
    O.valuation ((∑ k ∈ Finset.range m, z ^ k) - 1) < 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have : (∑ k ∈ Finset.range (n + 1), z ^ k) - 1 = z * ∑ k ∈ Finset.range n, z ^ k := by
    rw [Finset.sum_range_succ', pow_zero, add_sub_cancel_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => pow_succ' z k
  rw [this, map_mul]
  calc O.valuation z * O.valuation (∑ k ∈ Finset.range n, z ^ k) ≤ O.valuation z * 1 := by
        gcongr; exact (O.valuation_le_one_iff _).mpr (geom_mem O hz n)
    _ < 1 := by rwa [mul_one]

theorem valuation_le_valuation_geom (O : ValuationSubring F) {z : F} (hz : z ∉ O) {m : ℕ}
    (hm : 2 ≤ m) :
    (∑ k ∈ Finset.range m, z ^ k) ≠ 0 ∧
      O.valuation z ≤ O.valuation (∑ k ∈ Finset.range m, z ^ k) := by
  have h1 : 1 < O.valuation z := one_lt_valuation_of_not_mem O hz
  have hz0 : O.valuation z ≠ 0 := ne_zero_of_lt h1
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hlt : O.valuation (∑ k ∈ Finset.range (n + 1), z ^ k) < O.valuation (z ^ (n + 1)) := by
    apply Valuation.map_sum_lt
    · rw [map_pow]; exact pow_ne_zero _ hz0
    · intro k hk
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ h1 (Finset.mem_range.mp hk)
  have heq : O.valuation (∑ k ∈ Finset.range (n + 2), z ^ k) = O.valuation (z ^ (n + 1)) := by
    rw [Finset.sum_range_succ]
    exact Valuation.map_add_eq_of_lt_right _ hlt
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero, map_pow] at heq
    exact pow_ne_zero _ hz0 heq.symm
  · rw [heq, map_pow, pow_succ']
    calc O.valuation z = O.valuation z * 1 := (mul_one _).symm
      _ ≤ O.valuation z * O.valuation z ^ n := by gcongr; exact one_le_pow₀ h1.le

theorem geom_sum_ne_zero_of_not_dvd {K : Type*} [Field K] (a : K) [Decidable (a = 1)] {m : ℕ}
    (h : ¬ ((if a = 1 then ringChar K else orderOf a) ∣ m)) :
    (∑ k ∈ Finset.range m, a ^ k) ≠ 0 := by
  intro hs
  apply h
  split_ifs with ha
  · subst ha
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
    exact (ringChar.spec K m).mp hs
  · have hgeom := geom_sum_mul a m
    rw [hs, zero_mul, eq_comm, sub_eq_zero] at hgeom
    exact orderOf_dvd_of_pow_eq_one hgeom

theorem badMod_ne_one {K : Type*} [Field K] (a : K) [Decidable (a = 1)] :
    (if a = 1 then ringChar K else orderOf a) ≠ 1 := by
  split_ifs with ha
  · intro h1
    have h := ringChar.Nat.cast_ringChar (R := K)
    rw [h1, Nat.cast_one] at h
    exact one_ne_zero h
  · rwa [Ne, orderOf_eq_one_iff]

theorem exists_geom_sum_ne_zero {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ i, Field (κ i)]
    (a : ∀ i, κ i) : ∃ m : ℕ, 2 ≤ m ∧ ∀ i, (∑ k ∈ Finset.range m, a i ^ k) ≠ 0 := by
  classical
  let d : ι → ℕ := fun i => if a i = 1 then ringChar (κ i) else orderOf (a i)
  let M : ℕ := ∏ i, if d i = 0 then 1 else d i
  have hM : 0 < M := Finset.prod_pos fun i _ => by
    split_ifs with h <;> omega
  refine ⟨M + 1, by omega, fun i => geom_sum_ne_zero_of_not_dvd (a i) ?_⟩
  show ¬ d i ∣ M + 1
  intro hdvd
  by_cases h0 : d i = 0
  · rw [h0, zero_dvd_iff] at hdvd
    omega
  · have hdM : d i ∣ M := by
      have h : (if d i = 0 then 1 else d i) ∣ M :=
        Finset.dvd_prod_of_mem (fun i => if d i = 0 then 1 else d i) (Finset.mem_univ i)
      rwa [if_neg h0] at h
    have h1 : d i ∣ 1 := (Nat.dvd_add_right hdM).mp hdvd
    exact badMod_ne_one (a i) (Nat.dvd_one.mp h1)

theorem exists_mem_lt_one_not_mem (O₁ O₂ : ValuationSubring F) (h₁₂ : ¬ O₁ ≤ O₂)
    (h₂₁ : ¬ O₂ ≤ O₁) : ∃ t ∈ O₁, O₁.valuation t < 1 ∧ t ∉ O₂ := by
  by_contra H
  push Not at H
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.not_le_iff_exists.mp h₁₂
  apply h₂₁
  intro w hw₂
  by_contra hw₁
  have hw0 : w ≠ 0 := ne_zero_of_not_mem O₁ hw₁
  have hwinv : w⁻¹ ∈ O₁ := (O₁.mem_or_inv_mem w).resolve_left hw₁
  have hvw : O₁.valuation w⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ (one_lt_valuation_of_not_mem O₁ hw₁)
  have hlt : O₁.valuation (x * w⁻¹) < 1 := by
    rw [map_mul]
    calc O₁.valuation x * O₁.valuation w⁻¹ ≤ 1 * O₁.valuation w⁻¹ := by
          gcongr; exact (O₁.valuation_le_one_iff x).mpr hx₁
      _ < 1 := by rwa [one_mul]
  have ht : x * w⁻¹ ∈ O₂ := H _ (mul_mem hx₁ hwinv) hlt
  apply hx₂
  have : x = x * w⁻¹ * w := by rw [inv_mul_cancel_right₀ hw0]
  rw [this]
  exact mul_mem ht hw₂

theorem exists_lift {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F)
    (hinc : ∀ i l, i ≠ l → ¬ O' i ≤ O' l) (j : ι) {y : F} (hy : y ∈ O' j) :
    ∃ r : F, (∀ i, r ∈ O' i) ∧ (O' j).valuation (r - y) < 1 ∧
      ∀ i, i ≠ j → (O' i).valuation r < 1 := by
  classical

  have hA : ∀ l, ∃ t : F, l ≠ j → (t ∈ O' j ∧ (O' j).valuation t < 1 ∧ t ∉ O' l) := by
    intro l
    by_cases hl : l = j
    · exact ⟨0, fun h => (h hl).elim⟩
    · obtain ⟨t, ht, hv, hn⟩ :=
        exists_mem_lt_one_not_mem (O' j) (O' l) (hinc j l (Ne.symm hl)) (hinc l j hl)
      exact ⟨t, fun _ => ⟨ht, hv, hn⟩⟩
  choose t ht using hA

  let a : ∀ q : ι × ι, ResidueField (O' q.2) := fun q =>
    if h : t q.1 * y ∈ O' q.2 then residue (O' q.2) ⟨t q.1 * y, h⟩ else 0
  obtain ⟨m, hm2, hgood⟩ := exists_geom_sum_ne_zero (fun q : ι × ι => ResidueField (O' q.2)) a
  let u : ι → F := fun l => ∑ k ∈ Finset.range m, (t l * y) ^ k

  have hF1 : ∀ l i, t l * y ∈ O' i → u l ∈ O' i ∧ (O' i).valuation (u l) = 1 := by
    intro l i hz
    refine ⟨geom_mem _ hz m, valuation_eq_one_of_residue_ne_zero _ (geom_mem _ hz m) ?_⟩
    rw [residue_geom _ hz m]
    have := hgood (l, i)
    simp only [a, dif_pos hz] at this
    exact this

  have hF2 : ∀ l i, t l * y ∉ O' i → u l ≠ 0 ∧ (O' i).valuation (t l * y) ≤
      (O' i).valuation (u l) := fun l i hz => valuation_le_valuation_geom _ hz hm2

  have hF3 : ∀ l i, (u l)⁻¹ ∈ O' i := by
    intro l i
    by_cases hz : t l * y ∈ O' i
    · exact inv_mem_of_one_le _ (hF1 l i hz).2.ge
    · exact inv_mem_of_one_le _
        ((one_lt_valuation_of_not_mem _ hz).le.trans (hF2 l i hz).2)

  have hF4 : ∀ l, l ≠ j → (O' j).valuation ((u l)⁻¹ - 1) < 1 := by
    intro l hl
    obtain ⟨htj, hvt, -⟩ := ht l hl
    have hz : t l * y ∈ O' j := mul_mem htj hy
    have hvz : (O' j).valuation (t l * y) < 1 := by
      rw [map_mul]
      calc (O' j).valuation (t l) * (O' j).valuation y ≤ (O' j).valuation (t l) * 1 := by
            gcongr; exact ((O' j).valuation_le_one_iff y).mpr hy
        _ < 1 := by rwa [mul_one]
    exact (inv_sub_one _ (valuation_geom_sub_one_lt _ hz hvz (by omega : 1 ≤ m))).2.2

  have hkey : ∀ i, i ≠ j → (O' i).valuation (y * (u i)⁻¹) < 1 := by
    intro i hij
    obtain ⟨-, -, hti⟩ := ht i hij
    have h1t : 1 < (O' i).valuation (t i) := one_lt_valuation_of_not_mem _ hti
    by_contra hge
    rw [not_lt] at hge
    have hlt : 1 < (O' i).valuation (t i) * (O' i).valuation (y * (u i)⁻¹) :=
      one_lt_mul_of_lt_of_le' h1t hge
    rw [← map_mul, ← mul_assoc] at hlt
    by_cases hz : t i * y ∈ O' i
    · obtain ⟨-, hvu⟩ := hF1 i i hz
      have : (O' i).valuation (t i * y * (u i)⁻¹) ≤ 1 := by
        rw [map_mul, map_inv₀, hvu, inv_one, mul_one]
        exact ((O' i).valuation_le_one_iff _).mpr hz
      exact absurd hlt (not_lt.mpr this)
    · obtain ⟨hu0, hzu⟩ := hF2 i i hz
      have hvu0 : (O' i).valuation (u i) ≠ 0 := (map_ne_zero _).mpr hu0
      have : (O' i).valuation (t i * y * (u i)⁻¹) ≤ 1 := by
        rw [map_mul, map_inv₀]
        calc (O' i).valuation (t i * y) * ((O' i).valuation (u i))⁻¹
            ≤ (O' i).valuation (u i) * ((O' i).valuation (u i))⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ hvu0
      exact absurd hlt (not_lt.mpr this)

  have hR3 : ∀ i, i ≠ j →
      (O' i).valuation (y * ∏ l ∈ Finset.univ.erase j, (u l)⁻¹) < 1 := by
    intro i hij
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    rw [map_mul, map_prod, ← Finset.mul_prod_erase _ _ hi, ← mul_assoc]
    have hrest : ∏ l ∈ (Finset.univ.erase j).erase i, (O' i).valuation (u l)⁻¹ ≤ 1 :=
      Finset.prod_le_one' fun l _ => ((O' i).valuation_le_one_iff _).mpr (hF3 l i)
    calc (O' i).valuation y * (O' i).valuation (u i)⁻¹ *
          ∏ l ∈ (Finset.univ.erase j).erase i, (O' i).valuation (u l)⁻¹
        ≤ (O' i).valuation y * (O' i).valuation (u i)⁻¹ * 1 := by gcongr
      _ = (O' i).valuation (y * (u i)⁻¹) := by rw [mul_one, map_mul]
      _ < 1 := hkey i hij
  refine ⟨y * ∏ l ∈ Finset.univ.erase j, (u l)⁻¹, ?_, ?_, hR3⟩
  · intro i
    by_cases hij : i = j
    · subst hij
      exact mul_mem hy (prod_mem fun l _ => hF3 l i)
    · exact ((O' i).valuation_le_one_iff _).mp (hR3 i hij).le
  · have hP := prod_sub_one (O' j) (Finset.univ.erase j) (fun l => (u l)⁻¹)
      fun l hl => ⟨hF3 l j, hF4 l (Finset.ne_of_mem_erase hl)⟩
    have : y * ∏ l ∈ Finset.univ.erase j, (u l)⁻¹ - y =
        y * (∏ l ∈ Finset.univ.erase j, (u l)⁻¹ - 1) := by ring
    rw [this, map_mul]
    calc (O' j).valuation y * (O' j).valuation (∏ l ∈ Finset.univ.erase j, (u l)⁻¹ - 1)
        ≤ 1 * (O' j).valuation (∏ l ∈ Finset.univ.erase j, (u l)⁻¹ - 1) := by
          gcongr; exact ((O' j).valuation_le_one_iff y).mpr hy
      _ < 1 := by rw [one_mul]; exact hP.2

end valuationSubring

section algebraic

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

theorem eq_of_le_of_over [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    {O₁ O₂ : ValuationSubring F} (hle : O₁ ≤ O₂)
    (h₁ : ∀ x : E, algebraMap E F x ∈ O₁ ↔ x ∈ O)
    (h₂ : ∀ x : E, algebraMap E F x ∈ O₂ ↔ x ∈ O) : O₁ = O₂ := by
  classical
  refine le_antisymm hle ?_
  intro x hx₂
  by_contra hx₁
  have hx0 : x ≠ 0 := ne_zero_of_not_mem O₁ hx₁
  have hy₁ : x⁻¹ ∈ O₁ := (O₁.mem_or_inv_mem x).resolve_left hx₁
  have hvy : O₁.valuation x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ (one_lt_valuation_of_not_mem O₁ hx₁)
  have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0

  obtain ⟨p, hp0, hpy⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) x⁻¹
  set v := O₁.valuation with hvdef
  let τ : ℕ → F := fun k => algebraMap E F (p.coeff k) * x⁻¹ ^ k
  have hsum : ∑ k ∈ Finset.range (p.natDegree + 1), τ k = 0 := by
    simp only [τ]
    rw [Polynomial.aeval_eq_sum_range] at hpy
    simpa only [Algebra.smul_def] using hpy
  set T := (Finset.range (p.natDegree + 1)).filter fun k => p.coeff k ≠ 0 with hTdef
  have hmemT : ∀ k, k ∈ T → p.coeff k ≠ 0 := fun k hk => (Finset.mem_filter.mp hk).2
  have hT : ∑ k ∈ T, τ k = 0 := by
    rw [hTdef, Finset.sum_filter_of_ne]
    · exact hsum
    · intro k _ hk h0
      apply hk
      simp only [τ, h0, map_zero, zero_mul]
  have hτ0 : ∀ k ∈ T, τ k ≠ 0 := fun k hk =>
    mul_ne_zero ((map_ne_zero _).mpr (hmemT k hk)) (pow_ne_zero _ hy0)
  have hTne : T.Nonempty := ⟨p.natDegree, Finset.mem_filter.mpr ⟨Finset.self_mem_range_succ _,
    by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hp0⟩⟩
  obtain ⟨k₀, hk₀, hmax⟩ := T.exists_max_image (fun k => v (τ k)) hTne

  have hk₁ : ∃ k₁ ∈ T, k₁ ≠ k₀ ∧ v (τ k₁) = v (τ k₀) := by
    by_contra H
    push Not at H
    have hlt : ∀ k ∈ T.erase k₀, v (τ k) < v (τ k₀) := fun k hk =>
      lt_of_le_of_ne (hmax k (Finset.mem_of_mem_erase hk))
        (H k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
    have hne : v (τ k₀) ≠ 0 := (map_ne_zero v).mpr (hτ0 k₀ hk₀)
    have h1 : v (∑ k ∈ T.erase k₀, τ k) < v (τ k₀) := Valuation.map_sum_lt v hne hlt
    have h2 : v (∑ k ∈ T, τ k) = v (τ k₀) := by
      rw [← Finset.add_sum_erase T τ hk₀]
      exact Valuation.map_add_eq_of_lt_left _ h1
    rw [hT, map_zero] at h2
    exact hne h2.symm
  obtain ⟨k₁, hk₁T, hne, heqv⟩ := hk₁

  have key : ∀ a b : ℕ, a ∈ T → b ∈ T → a < b → v (τ a) = v (τ b) → False := by
    intro a b ha hb hab hv
    have hca : p.coeff a ≠ 0 := hmemT a ha
    have hcb : p.coeff b ≠ 0 := hmemT b hb
    have hc0 : p.coeff a / p.coeff b ≠ 0 := div_ne_zero hca hcb
    have hya : v (x⁻¹ ^ a) ≠ 0 := (map_ne_zero v).mpr (pow_ne_zero _ hy0)
    have hcb' : v (algebraMap E F (p.coeff b)) ≠ 0 :=
      (map_ne_zero v).mpr ((map_ne_zero _).mpr hcb)

    have hvc : v (algebraMap E F (p.coeff a / p.coeff b)) = v (x⁻¹ ^ (b - a)) := by
      have hpow : x⁻¹ ^ b = x⁻¹ ^ a * x⁻¹ ^ (b - a) := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le]
      have hv' : v (algebraMap E F (p.coeff a)) * v (x⁻¹ ^ a) =
          v (algebraMap E F (p.coeff b)) * (v (x⁻¹ ^ a) * v (x⁻¹ ^ (b - a))) := by
        have := hv
        simp only [τ, map_mul, hpow] at this
        exact this
      have h' : v (algebraMap E F (p.coeff a)) =
          v (x⁻¹ ^ (b - a)) * v (algebraMap E F (p.coeff b)) := by
        apply mul_right_cancel₀ hya
        rw [hv']; ac_rfl
      rw [map_div₀, map_div₀, div_eq_iff hcb', h']
    have hvc1 : v (algebraMap E F (p.coeff a / p.coeff b)) < 1 := by
      rw [hvc, map_pow]
      exact pow_lt_one₀ zero_le' hvy (Nat.sub_ne_zero_of_lt hab)

    have hcinv : (p.coeff a / p.coeff b)⁻¹ ∉ O := by
      intro hmem
      have h1' : algebraMap E F (p.coeff a / p.coeff b)⁻¹ ∈ O₁ := (h₁ _).mpr hmem
      rw [map_inv₀, ← O₁.valuation_le_one_iff, map_inv₀] at h1'
      have hc'0 : v (algebraMap E F (p.coeff a / p.coeff b)) ≠ 0 :=
        (map_ne_zero v).mpr ((map_ne_zero _).mpr hc0)
      exact not_lt.mpr h1' ((one_lt_inv₀ (zero_lt_iff.mpr hc'0)).mpr hvc1)

    obtain ⟨u, hu⟩ := (O₁.valuation_eq_iff _ _).mp hvc
    have hmem₂ : algebraMap E F (p.coeff a / p.coeff b)⁻¹ ∈ O₂ := by
      rw [map_inv₀, ← hu, mul_inv, ← inv_pow, inv_inv]
      refine mul_mem ?_ (pow_mem hx₂ _)
      have hmul : ((u : O₁) : F) * (((u⁻¹ : O₁ˣ) : O₁) : F) = 1 := by
        rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
      rw [inv_eq_of_mul_eq_one_right hmul]
      exact hle ((u⁻¹ : O₁ˣ) : O₁).2
    exact hcinv ((h₂ _).mp hmem₂)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key k₁ k₀ hk₁T hk₀ h heqv
  · exact key k₀ k₁ hk₀ hk₁T h heqv.symm

end algebraic

section linearAlgebra

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

theorem finite_and_finrank_le [FiniteDimensional E F] (O : ValuationSubring E)
    {V : Type*} [AddCommGroup V] [Module (ResidueField O) V] (S : Set F) (ψ : F → V)
    (hψ : ∀ (s : Finset V) (c : V → O) (y : V → F), (∀ v ∈ s, y v ∈ S) →
      ψ (∑ v ∈ s, algebraMap E F (c v) * y v) = ∑ v ∈ s, residue O (c v) • ψ (y v))
    (hsurj : ∀ w : V, ∃ x ∈ S, ψ x = w) :
    Module.Finite (ResidueField O) V ∧
      Module.finrank (ResidueField O) V ≤ Module.finrank E F := by
  classical
  choose y hyS hyψ using hsurj
  have hrank : Module.rank (ResidueField O) V ≤ Module.finrank E F := by
    apply rank_le
    intro s hs

    have hli : LinearIndependent E (fun i : s => y i) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      beta_reduce at hg
      by_contra hne
      push Not at hne
      obtain ⟨i₁, hi₁⟩ := hne
      obtain ⟨i₀, -, hmax⟩ :=
        Finset.univ.exists_max_image (fun i : s => O.valuation (g i)) ⟨i₁, Finset.mem_univ _⟩
      have hg0 : g i₀ ≠ 0 := by
        intro h0
        have h := hmax i₁ (Finset.mem_univ _)
        rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
        exact hi₁ h
      have hv0 : O.valuation (g i₀) ≠ 0 := (map_ne_zero _).mpr hg0
      have hmem : ∀ i, (g i₀)⁻¹ * g i ∈ O := by
        intro i
        rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
        calc (O.valuation (g i₀))⁻¹ * O.valuation (g i)
            ≤ (O.valuation (g i₀))⁻¹ * O.valuation (g i₀) := by
              gcongr; exact hmax i (Finset.mem_univ _)
          _ = 1 := inv_mul_cancel₀ hv0
      let c : V → O := fun v => if h : v ∈ s then ⟨(g i₀)⁻¹ * g ⟨v, h⟩, hmem ⟨v, h⟩⟩ else 0
      have hc : ∀ i : s, c i = ⟨(g i₀)⁻¹ * g i, hmem i⟩ := fun i => by
        simp only [c, dif_pos i.2, Subtype.coe_eta]
      have hsum : ∑ v ∈ s, algebraMap E F (c v) * y v = 0 := by
        rw [← Finset.sum_coe_sort]
        have : ∀ i : s, algebraMap E F (c i) * y i = algebraMap E F (g i₀)⁻¹ * (g i • y i) := by
          intro i
          rw [hc i, Algebra.smul_def, map_mul, mul_assoc]
        simp_rw [this]
        rw [← Finset.mul_sum, hg, mul_zero]
      have h0 : ψ 0 = 0 := by
        have := hψ ∅ c y (by simp)
        simpa using this
      have hrel : ∑ v ∈ s, residue O (c v) • ψ (y v) = 0 := by
        rw [← hψ s c y fun v _ => hyS v, hsum, h0]
      have hrel' : ∑ i : s, residue O (c i) • (i : V) = 0 := by
        rw [← Finset.sum_coe_sort] at hrel
        simpa only [hyψ] using hrel
      have h1 : residue O (c i₀) = 0 :=
        Fintype.linearIndependent_iff.mp hs (fun i => residue O (c i)) hrel' i₀
      rw [hc i₀] at h1
      have hone : (⟨(g i₀)⁻¹ * g i₀, hmem i₀⟩ : O) = 1 := Subtype.ext (inv_mul_cancel₀ hg0)
      rw [hone, map_one] at h1
      exact one_ne_zero h1
    have := hli.fintype_card_le_finrank
    simpa using this
  have hfin : Module.Finite (ResidueField O) V := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩

end linearAlgebra

theorem result {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
    (O : ValuationSubring E) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F)
    (hinj : Function.Injective O')
    (hO : ∀ (j : ι) (x : E), algebraMap E F x ∈ O' j ↔ x ∈ O)
    [∀ j, Algebra (ResidueField O) (ResidueField (O' j))]
    (hcompat : ∀ (j : ι) (a : O), algebraMap (ResidueField O) (ResidueField (O' j))
        (residue O a) = residue (O' j) ⟨algebraMap E F a, (hO j a).mpr a.2⟩) :
    (∀ j, FiniteDimensional (ResidueField O) (ResidueField (O' j))) ∧
      ∑ j, Module.finrank (ResidueField O) (ResidueField (O' j)) ≤ Module.finrank E F := by
  classical

  have hinc : ∀ i l, i ≠ l → ¬ O' i ≤ O' l := fun i l hil hle =>
    hil (hinj (eq_of_le_of_over O hle (hO i) (hO l)))

  let ψ : F → ∀ j, ResidueField (O' j) := fun x j =>
    if h : x ∈ O' j then residue (O' j) ⟨x, h⟩ else 0
  have hψ_mem : ∀ (x : F) (j : ι) (h : x ∈ O' j), ψ x j = residue (O' j) ⟨x, h⟩ :=
    fun x j h => dif_pos h
  let S : Set F := {x | ∀ j, x ∈ O' j}
  have hS : ∀ x, x ∈ S ↔ ∀ j, x ∈ O' j := fun x => Iff.rfl

  have hψ : ∀ (s : Finset (∀ j, ResidueField (O' j))) (c : (∀ j, ResidueField (O' j)) → O)
      (y : (∀ j, ResidueField (O' j)) → F), (∀ v ∈ s, y v ∈ S) →
      ψ (∑ v ∈ s, algebraMap E F (c v) * y v) = ∑ v ∈ s, residue O (c v) • ψ (y v) := by
    intro s c y hyS
    funext j
    have hmem : ∀ v ∈ s, algebraMap E F (c v) * y v ∈ O' j := fun v hv =>
      mul_mem ((hO j _).mpr (c v).2) ((hS _).mp (hyS v hv) j)
    have hsum_mem : (∑ v ∈ s, algebraMap E F (c v) * y v) ∈ O' j := sum_mem hmem
    rw [hψ_mem _ j hsum_mem, Finset.sum_apply]
    have heq : (⟨∑ v ∈ s, algebraMap E F (c v) * y v, hsum_mem⟩ : O' j) =
        ∑ v ∈ s.attach, (⟨algebraMap E F (c v), (hO j _).mpr (c v).2⟩ : O' j) *
          ⟨y v, (hS _).mp (hyS v v.2) j⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul]
      exact (Finset.sum_attach s fun v => algebraMap E F (c v) * y v).symm
    rw [heq, map_sum, ← Finset.sum_attach s fun v => (residue O (c v) • ψ (y v)) j]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_mul, Pi.smul_apply, hψ_mem _ j ((hS _).mp (hyS v v.2) j), Algebra.smul_def,
      hcompat j (c v)]

  have hsurj : ∀ w : ∀ j, ResidueField (O' j), ∃ x ∈ S, ψ x = w := by
    intro w
    have hr : ∀ j, ∃ r : F, (∀ i, r ∈ O' i) ∧ ψ r j = w j ∧ ∀ i, i ≠ j → ψ r i = 0 := by
      intro j
      obtain ⟨yj, hyj⟩ := residue_surjective (w j)
      obtain ⟨r, hrmem, hrj, hri⟩ := exists_lift O' hinc j yj.2
      refine ⟨r, hrmem, ?_, ?_⟩
      · rw [hψ_mem r j (hrmem j), ← hyj]
        exact (residue_mk_eq_residue_mk_iff (O' j) (hrmem j) yj.2).mpr hrj
      · intro i hij
        rw [hψ_mem r i (hrmem i)]
        exact (residue_mk_eq_zero_iff (O' i) (hrmem i)).mpr (hri i hij)
    choose r hrmem hrj hri using hr
    refine ⟨∑ j, r j, (hS _).mpr fun i => sum_mem fun j _ => hrmem j i, ?_⟩
    funext i
    have hmem : (∑ j, r j) ∈ O' i := sum_mem fun j _ => hrmem j i
    rw [hψ_mem _ i hmem]
    have heq : (⟨∑ j, r j, hmem⟩ : O' i) = ∑ j, (⟨r j, hrmem j i⟩ : O' i) :=
      Subtype.ext (by rw [AddSubmonoidClass.coe_finsetSum])
    rw [heq, map_sum, Finset.sum_eq_single i]
    · rw [← hψ_mem (r i) i (hrmem i i)]; exact hrj i
    · intro j _ hji
      rw [← hψ_mem (r j) i (hrmem j i)]; exact hri j i (Ne.symm hji)
    · intro h; exact (h (Finset.mem_univ i)).elim
  obtain ⟨hfin, hle⟩ := finite_and_finrank_le O S ψ hψ hsurj
  haveI := hfin
  have hfinj : ∀ j, FiniteDimensional (ResidueField O) (ResidueField (O' j)) := fun j =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := ResidueField O) (φ := fun j => ResidueField (O' j)) j)
      (LinearMap.proj_surjective j)
  refine ⟨hfinj, ?_⟩
  haveI : ∀ j, Module.Finite (ResidueField O) (ResidueField (O' j)) := hfinj
  rw [← Module.finrank_pi_fintype (ResidueField O) (M := fun j => ResidueField (O' j))]
  exact hle

end EsbLeGen

theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    (O : ValuationSubring E)
    {ι : Type*} [Fintype ι]
    (O' : ι → ValuationSubring F)
    (hinj : Function.Injective O')
    (hO : ∀ (j : ι) (x : E), algebraMap E F x ∈ O' j ↔ x ∈ O)
    [∀ j, Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))]
    (hcompat : ∀ (j : ι) (a : O), algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))
        (IsLocalRing.residue O a) = IsLocalRing.residue (O' j) ⟨algebraMap E F a, (hO j a).mpr a.2⟩) :
    (∀ j, FiniteDimensional (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))) ∧
      ∑ j, Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j)) ≤ Module.finrank E F :=
  EsbLeGen.result O O' hinj hO hcompat

end S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff
end P2MW
export P2MW.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff (solution)
