-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.property2_averaging
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T00:02:03.321985+00:00
-- url     : https://prove2.me/submissions/34856b9b-1e6d-41db-9ea5-98dd94d6ff96

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

open ObfImpossibility.PseudoOracle
open scoped BigOperators

-- The query-set representation follows Nickrobbins95's accepted lemma_B_1 formalization.
namespace ObfImpossibility.PseudoOracle.QTree
variable {K L : ℕ}

/-- The set of oracle points queried by the run of `t` against `G`. -/
def qset : QTree K L → (Fin K → Fin L) → Finset (Fin K)
  | out _, _ => ∅
  | query z k, G => insert z ((k (G z)).qset G)

theorem card_qset_le (t : QTree K L) (G : Fin K → Fin L) : (t.qset G).card ≤ t.depth := by
  induction t with
  | out b => simp [qset, depth]
  | query z k ih =>
    simp only [qset, depth]
    have h1 := Finset.card_insert_le z ((k (G z)).qset G)
    have h2 := ih (G z)
    have h3 := Finset.le_sup (f := fun y => (k y).depth) (Finset.mem_univ (G z))
    omega

theorem hits_eq_true_iff (t : QTree K L) (G : Fin K → Fin L) (A : Finset (Fin K)) :
    t.hits G A = true ↔ ∃ z ∈ t.qset G, z ∈ A := by
  induction t with
  | out b => simp [hits, qset]
  | query z k ih =>
    simp only [hits, qset, Bool.or_eq_true, decide_eq_true_eq, ih, Finset.mem_insert]
    constructor
    · rintro (h | ⟨w, hw, hwA⟩)
      · exact ⟨z, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr hw, hwA⟩
    · rintro ⟨w, (rfl | hw), hwA⟩
      · exact Or.inl hwA
      · exact Or.inr ⟨w, hw, hwA⟩

end ObfImpossibility.PseudoOracle.QTree

namespace WentaoAveraging

private lemma choose_ratio (n m r : ℕ) (hn : 0 < n) (hm : m ≤ n) (hr : r ≤ m) :
    ((n - r).choose (m - r) : ℝ) ≤ (n.choose m : ℝ) * ((m : ℝ) / n) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrm : r ≤ m := by omega
    have hrn : r < n := by omega
    have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast (by omega : 0 < n - r)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hmnr : (0 : ℝ) ≤ (m - r : ℕ) := Nat.cast_nonneg _
    have hrec :=  Nat.add_one_mul_choose_eq (n - (r + 1)) (m - (r + 1))
    rw [show n - (r + 1) + 1 = n - r by omega,
      show m - (r + 1) + 1 = m - r by omega] at hrec
    have rec' : ((n - r : ℕ) : ℝ) * ((n - (r + 1)).choose (m - (r + 1)) : ℝ) =
        ((n - r).choose (m - r) : ℝ) * (m - r : ℕ) := by exact_mod_cast hrec
    have ratio : ((m - r : ℕ) : ℝ) / (n - r : ℕ) ≤ (m : ℝ) / n := by
      rw [div_le_div_iff₀ hnr hn0, Nat.cast_sub hrm, Nat.cast_sub hrn.le]
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    calc
      _ = ((n - r).choose (m - r) : ℝ) * (((m - r : ℕ) : ℝ) / (n - r : ℕ)) := by
        rw [← mul_div_assoc]
        apply (eq_div_iff hnr.ne').mpr
        nlinarith [rec']
      _ ≤ ((n.choose m : ℝ) * ((m : ℝ) / n) ^ r) *
          (((m - r : ℕ) : ℝ) / (n - r : ℕ)) :=
        mul_le_mul_of_nonneg_right (ih hrm) (by positivity)
      _ ≤ ((n.choose m : ℝ) * ((m : ℝ) / n) ^ r) * ((m : ℝ) / n) :=
        mul_le_mul_of_nonneg_left ratio (by positivity)
      _ = _ := by rw [pow_succ]; ring

private lemma count_containing {α : Type} [DecidableEq α] (U A : Finset α)
    (hn : 0 < U.card) (m : ℕ) (hm : m ≤ U.card) (hA : A ⊆ U) :
    (((U.powersetCard m).filter (A ⊆ ·)).card : ℝ) ≤
      (U.card.choose m : ℝ) * ((m : ℝ) / U.card) ^ A.card := by
  by_cases hr : A.card ≤ m
  · rw [Finset.card_filter_powersetCard_subset A U m hA hr]
    exact choose_ratio U.card m A.card hn hm hr
  · have hempty : (U.powersetCard m).filter (A ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, hAT⟩ := Finset.mem_filter.mp hT
      have := Finset.card_le_card hAT
      have := (Finset.mem_powersetCard.mp hT).2
      omega
    rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity


private lemma expected_hits {K : ℕ} (hK : 0 < K) (m : ℕ) (hm : m ≤ K)
    (Q : Fin K → Finset (Fin K)) (hself : ∀ x, x ∉ Q x)
    (q : ℝ) (hQ : ∀ x, ((Q x).card : ℝ) ≤ q) :
    ∑ S ∈ (Finset.univ : Finset (Fin K)).powersetCard m,
        ((S.filter fun x => ∃ z ∈ Q x, z ∈ S).card : ℝ) ≤
      (K.choose m : ℝ) * m * (q * m / K) := by
  classical
  let P := (Finset.univ : Finset (Fin K)).powersetCard m
  have hlocal (S : Finset (Fin K)) :
      ((S.filter fun x => ∃ z ∈ Q x, z ∈ S).card : ℝ) ≤
        ∑ x : Fin K, ∑ z ∈ Q x, if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0 := by
    calc
      _ = ∑ x ∈ S, if ∃ z ∈ Q x, z ∈ S then (1 : ℝ) else 0 := by
        rw [Finset.card_filter]; push_cast; rfl
      _ ≤ ∑ x ∈ S, ∑ z ∈ Q x, if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs with hex
        · obtain ⟨z, hz, hzS⟩ := hex
          have hh := Finset.single_le_sum (f := fun z => if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0)
            (fun z _ => by positivity) hz
          simpa only [hx, hzS, and_self, if_true] using hh
        · positivity
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => by positivity)
  have hpair (x z : Fin K) (hz : z ∈ Q x) :
      ∑ S ∈ P, (if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0) ≤
        (K.choose m : ℝ) * ((m : ℝ) / K) ^ 2 := by
    have hzx : z ≠ x := by intro h; subst z; exact hself x hz
    have hc : ({x, z} : Finset (Fin K)).card = 2 := by simp [Ne.symm hzx]
    have hh := count_containing (Finset.univ : Finset (Fin K)) {x, z}
      (by simpa using hK) m (by simpa using hm) (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin, hc] at hh
    have heq : (∑ S ∈ P, if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0) =
        ((P.filter ({x, z} ⊆ ·)).card : ℝ) := by
      rw [Finset.card_filter]; push_cast
      apply Finset.sum_congr rfl
      intro S _
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [heq]
    exact hh
  calc
    _ ≤ ∑ S ∈ P, ∑ x : Fin K, ∑ z ∈ Q x,
        if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun S _ => hlocal S)
    _ = ∑ x : Fin K, ∑ z ∈ Q x, ∑ S ∈ P,
        if x ∈ S ∧ z ∈ S then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ ∑ x : Fin K, ∑ _z ∈ Q x, (K.choose m : ℝ) * ((m : ℝ) / K) ^ 2 := by
      exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z hz => hpair x z hz))
    _ = ∑ x : Fin K, ((Q x).card : ℝ) * ((K.choose m : ℝ) * ((m : ℝ) / K) ^ 2) := by
      simp
    _ ≤ ∑ _x : Fin K, q * ((K.choose m : ℝ) * ((m : ℝ) / K) ^ 2) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hQ x) (by positivity))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp
      <;> ring

private lemma markov {β : Type} (P : Finset β) (X : β → ℕ) (t : ℝ) (ht : 0 < t) :
    ((P.filter fun S => t < (X S : ℝ)).card : ℝ) * t ≤ ∑ S ∈ P, (X S : ℝ) := by
  calc
    _ = ∑ _S ∈ P.filter (fun S => t < (X S : ℝ)), t := by simp
    _ ≤ ∑ S ∈ P.filter (fun S => t < (X S : ℝ)), (X S : ℝ) :=
      Finset.sum_le_sum (fun S hS => (Finset.mem_filter.mp hS).2.le)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)

end WentaoAveraging

open WentaoAveraging in
theorem solution :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ K L : ℕ,
      ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        ∀ G : Fin K ↪ Fin L,
          (3 / 4 : ℝ) ≤
            ((((Finset.univ : Finset (Fin K)).powersetCard ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊).filter
                fun S => (((S.filter fun x => (D (G x)).hits G (S.erase x) = true).card : ℝ) ≤
                  4 * (K : ℝ) ^ (-(4 * δ)) * (S.card : ℝ))).card : ℝ) /
              ((K.choose ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊ : ℕ) : ℝ) := by
  classical
  intro δ hδ hδ1 K L D hD G
  have hα : (0 : ℝ) < 1 - 5 * δ := by linarith
  by_cases hKzero : K = 0
  · subst K
    simp only [Nat.cast_zero, Real.zero_rpow hα.ne', Nat.floor_zero,
      Finset.powersetCard_zero, Nat.choose_zero_right, Nat.cast_one, div_one]
    have he : ({∅} : Finset (Finset (Fin 0))).filter
        (fun S => ((S.filter fun x => (D (G x)).hits G (S.erase x) = true).card : ℝ) ≤
          4 * (0 : ℝ) ^ (-(4 * δ)) * S.card) = {∅} := by
      apply Finset.filter_eq_self.mpr
      intro S hS
      have hS0 : S = ∅ := Finset.mem_singleton.mp hS
      subst S
      simp
    rw [he]
    norm_num
  have hK : 0 < K := Nat.pos_of_ne_zero hKzero
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let m := ⌊(K : ℝ) ^ (1 - 5 * δ)⌋₊
  let P := (Finset.univ : Finset (Fin K)).powersetCard m
  let X (S : Finset (Fin K)) := (S.filter fun x => (D (G x)).hits G (S.erase x) = true).card
  let q : ℝ := (K : ℝ) ^ δ
  let r : ℝ := (K : ℝ) ^ (-(4 * δ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hmreal : (m : ℝ) ≤ (K : ℝ) ^ (1 - 5 * δ) := Nat.floor_le (by positivity)
  have hmK : m ≤ K := by
    have hp : (K : ℝ) ^ (1 - 5 * δ) ≤ (K : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hK1 (show 1 - 5 * δ ≤ 1 by linarith)
    exact_mod_cast hmreal.trans hp
  have hC : (0 : ℝ) < K.choose m := by exact_mod_cast Nat.choose_pos hmK
  have hcard (S : Finset (Fin K)) (hS : S ∈ P) : S.card = m :=
    (Finset.mem_powersetCard.mp hS).2
  by_cases hmzero : m = 0
  · change (3 / 4 : ℝ) ≤ _
    change (3 / 4 : ℝ) ≤
      ((P.filter fun S => (X S : ℝ) ≤ 4 * r * S.card).card : ℝ) / (K.choose m : ℝ)
    have he : P.filter (fun S => (X S : ℝ) ≤ 4 * r * S.card) = P := by
      apply Finset.filter_eq_self.mpr
      intro S hS
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by rw [hcard S hS, hmzero])
      subst S
      simp [X]
    rw [he]
    norm_num [P, hmzero]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hmzero
  let Q (x : Fin K) := ((D (G x)).qset G).erase x
  have hself : ∀ x, x ∉ Q x := by intro x; exact Finset.notMem_erase _ _
  have hQ : ∀ x, ((Q x).card : ℝ) ≤ q := by
    intro x
    calc
      _ ≤ (((D (G x)).qset G).card : ℝ) := by exact_mod_cast (Finset.card_erase_le (s := (D (G x)).qset G) (a := x))
      _ ≤ ((D (G x)).depth : ℝ) := by exact_mod_cast QTree.card_qset_le _ _
      _ ≤ q := hD (G x)
  have heq (S : Finset (Fin K)) :
      S.filter (fun x => (D (G x)).hits G (S.erase x) = true) =
        S.filter (fun x => ∃ z ∈ Q x, z ∈ S) := by
    apply Finset.filter_congr
    intro x _
    rw [QTree.hits_eq_true_iff]
    constructor
    · rintro ⟨z, hz, hzS⟩
      obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hzS
      exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩, hzS⟩
    · rintro ⟨z, hz, hzS⟩
      obtain ⟨hzx, hz⟩ := Finset.mem_erase.mp hz
      exact ⟨z, hz, Finset.mem_erase.mpr ⟨hzx, hzS⟩⟩
  have hratio : q * m / K ≤ r := by
    calc
      q * m / K ≤ q * (K : ℝ) ^ (1 - 5 * δ) / K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmreal hq.le) hKr.le
      _ = (K : ℝ) ^ (δ + (1 - 5 * δ) - 1) := by
        dsimp [q]
        conv_rhs => rw [Real.rpow_sub hKr, Real.rpow_add hKr, Real.rpow_one]
      _ = r := by dsimp [r]; congr 1 <;> ring
  have hsum : ∑ S ∈ P, (X S : ℝ) ≤ (K.choose m : ℝ) * m * r := by
    have h := expected_hits hK m hmK Q hself q hQ
    simp_rw [← heq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
  have hmark := markov P X (4 * r * m) (by positivity)
  have hbad : ((P.filter fun S => 4 * r * m < (X S : ℝ)).card : ℝ) ≤
      (K.choose m : ℝ) / 4 := by
    have hle := hmark.trans hsum
    nlinarith [mul_pos hr hmpos]
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun S => (X S : ℝ) ≤ 4 * r * m)
  simp only [not_le] at hsplit
  have hP : P.card = K.choose m := by simp [P]
  rw [hP] at hsplit
  have hgood : (3 / 4 : ℝ) * (K.choose m : ℝ) ≤
      ((P.filter fun S => (X S : ℝ) ≤ 4 * r * m).card : ℝ) := by
    have hs : ((P.filter fun S => (X S : ℝ) ≤ 4 * r * m).card : ℝ) +
        ((P.filter fun S => 4 * r * m < (X S : ℝ)).card : ℝ) = (K.choose m : ℝ) := by
      exact_mod_cast hsplit
    linarith
  have hfilters : P.filter (fun S => (X S : ℝ) ≤ 4 * r * S.card) =
      P.filter (fun S => (X S : ℝ) ≤ 4 * r * m) := by
    apply Finset.filter_congr
    intro S hS
    rw [hcard S hS]
  change (3 / 4 : ℝ) ≤
    ((P.filter fun S => (X S : ℝ) ≤ 4 * r * S.card).card : ℝ) / (K.choose m : ℝ)
  rw [hfilters, le_div_iff₀ hC]
  exact hgood
