-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P15.iWeight_rank_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:18:54.53861+00:00
-- url     : https://prove2.me/submissions/f8bb8703-e265-4508-86bd-91313c1a2a9f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators

namespace X6R15I

open QAlgorithms.Papers.Independent.Renew46.P15

/-! ### lexicographic order -/

theorem wlt_irrefl {n : ℕ} (a : Fin (n + 2) → ℕ) : ¬ weightLt a a := by
  rintro ⟨i, _, h⟩; exact lt_irrefl _ h

theorem wlt_trans {n : ℕ} {a b c : Fin (n + 2) → ℕ} (h1 : weightLt a b) (h2 : weightLt b c) :
    weightLt a c := by
  obtain ⟨i, hi, hab⟩ := h1
  obtain ⟨j, hj, hbc⟩ := h2
  rcases lt_trichotomy i j with h | rfl | h
  · exact ⟨i, fun k hk => (hi k hk).trans (hj k (hk.trans h)), hab.trans_eq (hj i h)⟩
  · exact ⟨i, fun k hk => (hi k hk).trans (hj k hk), hab.trans hbc⟩
  · exact ⟨j, fun k hk => (hi k (hk.trans h)).trans (hj k hk), (hi j h).trans_lt hbc⟩

theorem wlt_total {n : ℕ} {a b : Fin (n + 2) → ℕ} (h : a ≠ b) : weightLt a b ∨ weightLt b a := by
  classical
  have hne : (Finset.univ.filter fun i => a i ≠ b i).Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h'
    exact h (funext fun i => by simpa using h' (Finset.mem_univ i))
  set i := (Finset.univ.filter fun i => a i ≠ b i).min' hne
  have hi : a i ≠ b i := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
  have hpre : ∀ j, j < i → a j = b j := by
    intro j hj
    by_contra hc
    have hjm : j ∈ Finset.univ.filter fun i => a i ≠ b i := by simp [hc]
    have := Finset.min'_le _ j hjm
    exact absurd hj (not_lt.2 this)
  rcases lt_or_gt_of_ne hi with h1 | h1
  · exact Or.inl ⟨i, hpre, h1⟩
  · exact Or.inr ⟨i, fun j hj => (hpre j hj).symm, h1⟩

theorem wlt_cons {n : ℕ} (a b : ℕ) (x y : Fin (n + 2) → ℕ) :
    weightLt (n := n + 1) (Fin.cons a x) (Fin.cons b y) ↔ a < b ∨ (a = b ∧ weightLt x y) := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    induction i using Fin.cases with
    | zero => left; simpa using hlt
    | succ j =>
      right
      refine ⟨by simpa using hi 0 (Fin.succ_pos j), j, fun k hk => ?_, by simpa using hlt⟩
      simpa using hi k.succ (Fin.succ_lt_succ_iff.2 hk)
  · rintro (h | ⟨rfl, j, hj, hlt⟩)
    · exact ⟨0, fun k hk => absurd hk (Fin.not_lt_zero k), by simpa using h⟩
    · refine ⟨j.succ, fun k hk => ?_, by simpa using hlt⟩
      induction k using Fin.cases with
      | zero => rfl
      | succ k => simpa using hj k (Fin.succ_lt_succ_iff.1 hk)

theorem anti_cons {n : ℕ} (a : ℕ) (y : Fin (n + 2) → ℕ) :
    Antitone (Fin.cons a y : Fin (n + 3) → ℕ) ↔ y 0 ≤ a ∧ Antitone y := by
  constructor
  · intro h
    refine ⟨by simpa using h (Fin.zero_le (1 : Fin (n + 3))), fun i j hij => ?_⟩
    simpa using h (Fin.succ_le_succ_iff.2 hij)
  · rintro ⟨h0, hy⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using (hy (Fin.zero_le j)).trans h0
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp [Fin.le_def])
      | succ j => simpa using hy (Fin.succ_le_succ_iff.1 hij)

/-! ### the domain and bounded counts -/

def Dom (n : ℕ) : Set (Fin (n + 2) → ℕ) := {x | Antitone x ∧ x (Fin.last (n + 1)) = 0}

def Bnd (n v : ℕ) : Set (Fin (n + 2) → ℕ) := {x | x ∈ Dom n ∧ x 0 < v}

theorem box_finite (k v : ℕ) : {x : Fin k → ℕ | ∀ i, x i < v}.Finite := by
  have : {x : Fin k → ℕ | ∀ i, x i < v} = Set.pi Set.univ (fun _ => Set.Iio v) := by
    ext x; simp
  rw [this]
  exact Set.Finite.pi fun _ => Set.finite_Iio v

theorem Bnd_finite (n v : ℕ) : (Bnd n v).Finite := by
  refine (box_finite (n + 2) v).subset fun x hx => fun i => ?_
  exact lt_of_le_of_lt (hx.1.1 (Fin.zero_le i)) hx.2

theorem cons_mem_Dom {n : ℕ} (a : ℕ) (y : Fin (n + 2) → ℕ) :
    (Fin.cons a y : Fin (n + 3) → ℕ) ∈ Dom (n + 1) ↔ y ∈ Dom n ∧ y 0 ≤ a := by
  simp only [Dom, Set.mem_setOf_eq, anti_cons]
  have : (Fin.cons a y : Fin (n + 3) → ℕ) (Fin.last (n + 2)) = y (Fin.last (n + 1)) := by
    rw [← Fin.succ_last]; rfl
  rw [this]; tauto

theorem Dom_cons {n : ℕ} (x : Fin (n + 3) → ℕ) : x = Fin.cons (x 0) (Fin.tail x) :=
  (Fin.cons_self_tail x).symm

theorem cinj (m v : ℕ) :
    Function.Injective (fun y : Fin (m + 2) → ℕ => (Fin.cons v y : Fin (m + 3) → ℕ)) :=
  fun a b h => by simpa using congrArg Fin.tail h

theorem Bnd_zero (n : ℕ) : Bnd n 0 = ∅ := by
  ext x; simp [Bnd]

theorem Bnd_base (v : ℕ) : (Bnd 0 v).ncard = v := by
  have : Bnd 0 v = (fun j : ℕ => (![j, 0] : Fin 2 → ℕ)) '' Set.Iio v := by
    ext x
    simp only [Bnd, Dom, Set.mem_setOf_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨⟨_, hl⟩, h0⟩
      refine ⟨x 0, h0, ?_⟩
      ext i; fin_cases i
      · rfl
      · simpa using hl.symm
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨fun i k hik => ?_, rfl⟩, hj⟩
      fin_cases i <;> fin_cases k <;> simp_all [Fin.le_def]
  rw [this, Set.ncard_image_of_injective _ (fun a b h => by simpa using congrFun h 0)]
  simp

theorem Bnd_succ (m v : ℕ) :
    Bnd (m + 1) (v + 1) = Bnd (m + 1) v ∪ (Fin.cons v) '' (Bnd m (v + 1)) := by
  ext x
  constructor
  · rintro ⟨hx, h0⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h0 with h | h
    · exact Or.inl ⟨hx, h⟩
    · right
      refine ⟨Fin.tail x, ?_, ?_⟩
      · rw [Dom_cons x, cons_mem_Dom] at hx
        exact ⟨hx.1, by rw [← h]; exact Nat.lt_succ_of_le hx.2⟩
      · rw [← h]; exact (Fin.cons_self_tail x)
  · rintro (⟨hx, h0⟩ | ⟨y, ⟨hy, hy0⟩, rfl⟩)
    · exact ⟨hx, h0.trans (Nat.lt_succ_self v)⟩
    · refine ⟨(cons_mem_Dom v y).2 ⟨hy, Nat.lt_succ_iff.1 hy0⟩, by simp⟩

theorem Bnd_card (m v : ℕ) : (Bnd m v).ncard = Nat.choose (m + 1 + v - 1) (m + 1) := by
  induction m generalizing v with
  | zero =>
    rw [Bnd_base]; simp
  | succ m ih =>
    induction v with
    | zero => rw [Bnd_zero]; simp
    | succ v ihv =>
      rw [Bnd_succ, Set.ncard_union_eq _ (Bnd_finite _ _) ((Bnd_finite _ _).image _),
        Set.ncard_image_of_injective _ (cinj m v), ihv, ih]
      · have e1 : m + 1 + 1 + (v + 1) - 1 = (m + 1 + v) + 1 := by omega
        have e2 : m + 1 + 1 + v - 1 = m + 1 + v := by omega
        have e3 : m + 1 + (v + 1) - 1 = m + 1 + v := by omega
        rw [e1, e2, e3, Nat.choose_succ_succ', add_comm]
      · rw [Set.disjoint_left]
        rintro x ⟨_, hx0⟩ ⟨y, _, rfl⟩
        simp at hx0

/-! ### down-sets -/

def LtS (n : ℕ) (s : Fin (n + 2) → ℕ) : Set (Fin (n + 2) → ℕ) := {x | x ∈ Dom n ∧ weightLt x s}

theorem wlt_head_le {n : ℕ} {x s : Fin (n + 2) → ℕ} (h : weightLt x s) : x 0 ≤ s 0 := by
  obtain ⟨i, hi, hlt⟩ := h
  by_cases h0 : i = 0
  · subst h0; exact hlt.le
  · exact (hi 0 (Fin.pos_iff_ne_zero.2 h0)).le

theorem LtS_sub {n : ℕ} (s : Fin (n + 2) → ℕ) : LtS n s ⊆ Bnd n (s 0 + 1) :=
  fun x hx => ⟨hx.1, Nat.lt_succ_of_le (wlt_head_le hx.2)⟩

theorem LtS_finite {n : ℕ} (s : Fin (n + 2) → ℕ) : (LtS n s).Finite :=
  (Bnd_finite _ _).subset (LtS_sub s)

theorem rank_eq {n : ℕ} (s : GTTopRow n) : weightRank s = (LtS n s.val).ncard := by
  classical
  unfold weightRank
  set F := Finset.univ.filter fun a : Fin (n + 2) → Fin (s.val 0 + 1) =>
    Antitone (fun i => (a i).val) ∧ (a (Fin.last (n + 1))).val = 0 ∧
      weightLt (fun i => (a i).val) s.val
  have hinj : Function.Injective (fun (a : Fin (n + 2) → Fin (s.val 0 + 1)) i => (a i).val) :=
    fun a b h => funext fun i => Fin.val_injective (congrFun h i)
  have hset : LtS n s.val = (fun (a : Fin (n + 2) → Fin (s.val 0 + 1)) i => (a i).val) '' ↑F := by
    ext x
    constructor
    · rintro ⟨⟨hanti, hlast⟩, hlt⟩
      have hb : ∀ i, x i < s.val 0 + 1 := fun i =>
        Nat.lt_succ_of_le ((hanti (Fin.zero_le i)).trans (wlt_head_le hlt))
      refine ⟨fun i => ⟨x i, hb i⟩, ?_, rfl⟩
      simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨hanti, hlast, hlt⟩
    · rintro ⟨a, ha, rfl⟩
      simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
      exact ⟨⟨ha.1, ha.2.1⟩, ha.2.2⟩
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]

theorem LtS_cons {n : ℕ} (s : Fin (n + 3) → ℕ) (hs : s ∈ Dom (n + 1)) :
    LtS (n + 1) s = Bnd (n + 1) (s 0) ∪
      (fun y : Fin (n + 2) → ℕ => (Fin.cons (s 0) y : Fin (n + 3) → ℕ)) '' LtS n (Fin.tail s) := by
  have hs' := hs
  rw [Dom_cons s, cons_mem_Dom] at hs'
  ext x
  constructor
  · rintro ⟨hx, hlt⟩
    have hx' := hx
    rw [Dom_cons x, cons_mem_Dom] at hx'
    rw [Dom_cons x, Dom_cons s, wlt_cons] at hlt
    rcases hlt with h | ⟨h, h2⟩
    · exact Or.inl ⟨hx, h⟩
    · right
      refine ⟨Fin.tail x, ⟨hx'.1, h2⟩, ?_⟩
      simp only; rw [← h]; exact Fin.cons_self_tail x
  · rintro (⟨hx, h⟩ | ⟨y, ⟨hy, hlt⟩, rfl⟩)
    · refine ⟨hx, ?_⟩
      rw [Dom_cons x, Dom_cons s, wlt_cons]
      exact Or.inl h
    · refine ⟨(cons_mem_Dom _ _).2 ⟨hy, (wlt_head_le hlt).trans ?_⟩, ?_⟩
      · exact hs.1 (Fin.zero_le _)
      · conv_rhs => rw [Dom_cons s]
        rw [wlt_cons]
        exact Or.inr ⟨rfl, hlt⟩

def RF (n : ℕ) (s : Fin (n + 2) → ℕ) : ℕ :=
  ∑ k : Fin (n + 1), Nat.choose (n + 1 - k.val + s k.castSucc - 1) (n + 1 - k.val)

theorem LtS_card : ∀ (n : ℕ) (s : Fin (n + 2) → ℕ), s ∈ Dom n → (LtS n s).ncard = RF n s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    have : LtS 0 s = Bnd 0 (s 0) := by
      ext x
      constructor
      · rintro ⟨hx, i, hi, hlt⟩
        refine ⟨hx, ?_⟩
        fin_cases i
        · exact hlt
        · exfalso
          have h1 : x 1 = 0 := hx.2
          have h2 : s 1 = 0 := hs.2
          simp only [Fin.mk_one, Fin.isValue] at hlt
          omega
      · rintro ⟨hx, h⟩
        exact ⟨hx, 0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
    rw [this, Bnd_card]
    simp [RF]
  | succ n ih =>
    intro s hs
    have hs' := hs
    rw [Dom_cons s, cons_mem_Dom] at hs'
    rw [LtS_cons s hs, Set.ncard_union_eq _ (Bnd_finite _ _) ((LtS_finite _).image _),
      Set.ncard_image_of_injective _ (cinj n (s 0)), Bnd_card, ih _ hs'.1]
    · unfold RF
      conv_rhs => rw [Fin.sum_univ_succ]
      refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun k _ => ?_)
      · simp
      simp only [Fin.val_succ, Fin.tail]
      have e : n + 1 + 1 - (k.val + 1) = n + 1 - k.val := by omega
      rw [e, ← Fin.succ_castSucc]
    · rw [Set.disjoint_left]
      rintro x ⟨_, hx0⟩ ⟨y, _, rfl⟩
      simp at hx0

/-! ### order and bijection -/

theorem rank_lt {n : ℕ} {a b : GTTopRow n} (h : weightLt a.val b.val) :
    weightRank a < weightRank b := by
  rw [rank_eq, rank_eq]
  apply Set.ncard_lt_ncard _ (LtS_finite _)
  refine ⟨fun x hx => ⟨hx.1, wlt_trans hx.2 h⟩, fun hsub => wlt_irrefl _ (hsub ⟨a.2, h⟩).2⟩

theorem rank_iff {n : ℕ} (a b : GTTopRow n) : weightLt a.val b.val ↔ weightRank a < weightRank b := by
  refine ⟨rank_lt, fun h => ?_⟩
  by_contra hn
  by_cases hab : a.val = b.val
  · have : a = b := Subtype.ext hab
    subst this; exact lt_irrefl _ h
  · rcases wlt_total hab with h1 | h1
    · exact hn h1
    · exact absurd (rank_lt h1) (not_lt.2 h.le)

theorem rank_inj {n : ℕ} : Function.Injective (weightRank (n := n)) := by
  intro a b h
  by_contra hab
  have hv : a.val ≠ b.val := fun h' => hab (Subtype.ext h')
  rcases wlt_total hv with h1 | h1
  · exact absurd h (rank_lt h1).ne
  · exact absurd h (rank_lt h1).ne'

theorem ncard_Iio (r : ℕ) : (Set.Iio r).ncard = r := by
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

theorem lastne {n : ℕ} : Fin.last (n + 1) ≠ 0 := fun h =>
  absurd (congrArg Fin.val h) (by rw [Fin.val_last, Fin.val_zero]; omega)

theorem rank_surj {n : ℕ} : Function.Surjective (weightRank (n := n)) := by
  intro q
  let bv : Fin (n + 2) → ℕ := fun i => if i = 0 then q + 1 else 0
  have hb : Antitone bv ∧ bv (Fin.last (n + 1)) = 0 := by
    refine ⟨fun i j hij => ?_, ?_⟩
    · by_cases hj : j = 0
      · subst hj
        have : i = 0 := le_antisymm hij (Fin.zero_le _)
        subst this; exact le_rfl
      · simp [bv, hj]
    · show (if Fin.last (n + 1) = 0 then q + 1 else 0) = 0
      exact if_neg lastne
  let b : GTTopRow n := ⟨bv, hb⟩
  let S : Set (GTTopRow n) := {x | weightLt x.val bv}
  have hS : Subtype.val '' S = LtS n bv := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
    · rintro ⟨hx, hlt⟩; exact ⟨⟨x, hx⟩, hlt, rfl⟩
  have hcard : S.ncard = weightRank b := by
    rw [rank_eq, ← hS, Set.ncard_image_of_injective _ Subtype.val_injective]
  have himg : weightRank '' S = Set.Iio (weightRank b) := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact rank_lt hx
    · rw [Set.ncard_image_of_injOn rank_inj.injOn, hcard, ncard_Iio]
    · exact Set.finite_Iio _
  have hq : q < weightRank b := by
    rw [rank_eq]
    show q < (LtS n bv).ncard
    let f : ℕ → Fin (n + 2) → ℕ := fun j i => if i = 0 then j else 0
    have hf : Function.Injective f := fun x y h => by simpa [f] using congrFun h 0
    have hsub : f '' Set.Iio (q + 1) ⊆ LtS n bv := by
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨⟨fun i k hik => ?_, if_neg lastne⟩, 0, fun k hk => absurd hk (Fin.not_lt_zero k),
        by simpa [f, bv] using hj⟩
      by_cases hk : k = 0
      · subst hk
        have : i = 0 := le_antisymm hik (Fin.zero_le _)
        subst this; exact le_rfl
      · simp [f, hk]
    have := Set.ncard_le_ncard hsub (LtS_finite _)
    rw [Set.ncard_image_of_injective _ hf, ncard_Iio] at this
    omega
  have : q ∈ weightRank '' S := by rw [himg]; exact hq
  obtain ⟨x, _, hx⟩ := this
  exact ⟨x, hx⟩

theorem main (n : ℕ) :
    (∀ s : GTTopRow n, weightRank s = weightRankFormula s.val) ∧
    Function.Bijective (weightRank (n := n)) ∧
    ∀ a b : GTTopRow n, weightLt a.val b.val ↔ weightRank a < weightRank b :=
  ⟨fun s => (rank_eq s).trans (LtS_card n s.val s.2), ⟨rank_inj, rank_surj⟩, rank_iff⟩

end X6R15I

theorem solution (n : ℕ) :
    (∀ s : QAlgorithms.Papers.Independent.Renew46.P15.GTTopRow n,
      QAlgorithms.Papers.Independent.Renew46.P15.weightRank s =
        QAlgorithms.Papers.Independent.Renew46.P15.weightRankFormula s.val) ∧
    Function.Bijective (QAlgorithms.Papers.Independent.Renew46.P15.weightRank (n := n)) ∧
    ∀ a b : QAlgorithms.Papers.Independent.Renew46.P15.GTTopRow n,
      QAlgorithms.Papers.Independent.Renew46.P15.weightLt a.val b.val ↔
        QAlgorithms.Papers.Independent.Renew46.P15.weightRank a <
          QAlgorithms.Papers.Independent.Renew46.P15.weightRank b :=
  X6R15I.main n
