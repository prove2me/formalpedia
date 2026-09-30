-- Prove2me | solution 1 for SerfozoStochasticNetworks.kolmogorov_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:20:45.733981+00:00
-- url     : https://prove2.me/submissions/a33deca2-ef6c-4501-b4e3-ab79a580810a

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

open Finset

variable {E : Type*}

/-- A tuple `p₀, …, p_n` read as a sequence on `ℕ` (constant after `p_n`). -/
def kcSeq {n : ℕ} (p : Fin (n + 1) → E) (k : ℕ) : E :=
  if h : k ≤ n then p ⟨k, Nat.lt_succ_of_le h⟩ else p (Fin.last n)

lemma kcSeq_val {n : ℕ} (p : Fin (n + 1) → E) (i : Fin (n + 1)) : kcSeq p i = p i := by
  unfold kcSeq
  rw [dif_pos (Nat.lt_succ_iff.mp i.isLt)]

lemma kcSeq_zero {n : ℕ} (p : Fin (n + 1) → E) : kcSeq p 0 = p 0 := by
  simpa using kcSeq_val p 0

lemma kcSeq_last {n : ℕ} (p : Fin (n + 1) → E) : kcSeq p n = p (Fin.last n) :=
  kcSeq_val p (Fin.last n)

/-- Products along a tuple as products over `range`. -/
lemma kc_prod {n : ℕ} (p : Fin (n + 1) → E) (g : E → E → ℝ) :
    ∏ i : Fin n, g (p i.castSucc) (p i.succ) =
      ∏ k ∈ range n, g (kcSeq p k) (kcSeq p (k + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun k => g (kcSeq p k) (kcSeq p (k + 1))) n]
  refine prod_congr rfl fun i _ => ?_
  have h1 : kcSeq p (i : ℕ) = p i.castSucc := kcSeq_val p i.castSucc
  have h2 : kcSeq p ((i : ℕ) + 1) = p i.succ := kcSeq_val p i.succ
  show _ = g (kcSeq p (i : ℕ)) (kcSeq p ((i : ℕ) + 1))
  rw [h1, h2]

/-- Products along the tuple of a sequence. -/
lemma kc_tup_prod (C : ℕ → E) (N : ℕ) (g : E → E → ℝ) :
    ∏ i : Fin N, g (C (i.castSucc : Fin (N + 1))) (C (i.succ : Fin (N + 1))) =
      ∏ k ∈ range N, g (C k) (C (k + 1)) :=
  Fin.prod_univ_eq_prod_range (fun k => g (C k) (C (k + 1))) N

lemma kc_path_seq (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) (hp : IsPath q p) :
    ∀ k < n, 0 < q (kcSeq p k) (kcSeq p (k + 1)) := by
  intro k hk
  have h1 : kcSeq p k = p (Fin.castSucc ⟨k, hk⟩) := kcSeq_val p (Fin.castSucc ⟨k, hk⟩)
  have h2 : kcSeq p (k + 1) = p (Fin.succ ⟨k, hk⟩) := kcSeq_val p (Fin.succ ⟨k, hk⟩)
  rw [h1, h2]
  exact hp ⟨k, hk⟩

lemma kc_seq_path (q : E → E → ℝ) (C : ℕ → E) (N : ℕ)
    (h : ∀ k < N, 0 < q (C k) (C (k + 1))) : IsPath q (fun i : Fin (N + 1) => C i) :=
  fun i => h i i.isLt

lemma kc_ratio_pos (q : E → E → ℝ) (htw : TwoWay q) {n : ℕ} (p : Fin (n + 1) → E)
    (hp : IsPath q p) : 0 < pathRatio q p :=
  prod_pos fun i _ => div_pos (hp i) ((htw _ _).mp (hp i))

/-- Detailed balance gives Kolmogorov's criterion on every closed sequence of states. -/
lemma kc_rev_kol (q : E → E → ℝ) (h : IsReversible q) : KolmogorovCriterion q := by
  obtain ⟨π, hπ, hdb⟩ := h
  intro n p hp
  have e1 : pathRate q p = ∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1)) := kc_prod p q
  have e2 : pathRateRev q p = ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    kc_prod p (fun a b => q b a)
  rw [e1, e2]
  have hP : kcSeq p 0 = kcSeq p n := by rw [kcSeq_zero, kcSeq_last, hp]
  have key : (∏ k ∈ range n, π (kcSeq p k)) * ∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1)) =
      (∏ k ∈ range n, π (kcSeq p (k + 1))) * ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => hdb _ _
  have hsame : ∏ k ∈ range n, π (kcSeq p k) = ∏ k ∈ range n, π (kcSeq p (k + 1)) := by
    have f1 : ∏ k ∈ range (n + 1), π (kcSeq p k) =
        (∏ k ∈ range n, π (kcSeq p k)) * π (kcSeq p n) := prod_range_succ _ _
    have f2 : ∏ k ∈ range (n + 1), π (kcSeq p k) =
        (∏ k ∈ range n, π (kcSeq p (k + 1))) * π (kcSeq p 0) := prod_range_succ' _ _
    rw [f1, hP] at f2
    exact mul_right_cancel₀ (hπ _).ne' f2
  have hpos : 0 < ∏ k ∈ range n, π (kcSeq p (k + 1)) := prod_pos fun k _ => hπ _
  rw [hsame] at key
  exact mul_left_cancel₀ hpos.ne' key

/-- The reversal of `p'` followed by `p`, as a sequence on `ℕ`. -/
def kcJoin {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (i : ℕ) : E :=
  if i ≤ n' then kcSeq p' (n' - i) else kcSeq p (i - n')

lemma kcJoin_add {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (h0 : p 0 = p' 0)
    (k : ℕ) : kcJoin p p' (n' + k) = kcSeq p k := by
  unfold kcJoin
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.add_zero, if_pos le_rfl, Nat.sub_self, kcSeq_zero, kcSeq_zero, h0]
  · rw [if_neg (show ¬ (n' + k ≤ n') by omega), Nat.add_sub_cancel_left]

lemma kc_reflect (P' : ℕ → E) (n' : ℕ) (g : E → E → ℝ) :
    ∏ k ∈ range n', g (P' (n' - k)) (P' (n' - (k + 1))) =
      ∏ j ∈ range n', g (P' (j + 1)) (P' j) := by
  have h := prod_range_reflect (fun j => g (P' (j + 1)) (P' j)) n'
  have h' : ∏ j ∈ range n', g (P' (n' - 1 - j + 1)) (P' (n' - 1 - j)) =
      ∏ j ∈ range n', g (P' (j + 1)) (P' j) := h
  rw [← h']
  refine prod_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have e1 : n' - 1 - k + 1 = n' - k := by omega
  have e2 : n' - 1 - k = n' - (k + 1) := by omega
  rw [e1, e2]

lemma kc_join_prod {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (h0 : p 0 = p' 0)
    (g : E → E → ℝ) :
    ∏ k ∈ range (n' + n), g (kcJoin p p' k) (kcJoin p p' (k + 1)) =
      (∏ j ∈ range n', g (kcSeq p' (j + 1)) (kcSeq p' j)) *
        ∏ k ∈ range n, g (kcSeq p k) (kcSeq p (k + 1)) := by
  rw [prod_range_add, ← kc_reflect (kcSeq p') n' g]
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    unfold kcJoin
    rw [if_pos (show k ≤ n' by omega), if_pos (show k + 1 ≤ n' by omega)]
  · refine prod_congr rfl fun k _ => ?_
    have h1 := kcJoin_add p p' h0 k
    have h2 : kcJoin p p' (n' + k + 1) = kcSeq p (k + 1) := kcJoin_add p p' h0 (k + 1)
    rw [h1, h2]

/-- Kolmogorov's criterion gives the invariance of the ratio products along paths. -/
lemma kc_kol_ri (q : E → E → ℝ) (htw : TwoWay q) (h : KolmogorovCriterion q) :
    RatioInvariance q := by
  intro n n' p p' hp hp' h0 hl
  have hcl : kcJoin p p' 0 = kcJoin p p' (n' + n) := by
    rw [kcJoin_add p p' h0 n, kcSeq_last, hl]
    unfold kcJoin
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, kcSeq_last]
  have hK := h (n' + n) (fun i => kcJoin p p' i) (by simpa using hcl)
  have e1 : pathRate q (fun i : Fin (n' + n + 1) => kcJoin p p' i) =
      ∏ k ∈ range (n' + n), q (kcJoin p p' k) (kcJoin p p' (k + 1)) :=
    kc_tup_prod (kcJoin p p') (n' + n) q
  have e2 : pathRateRev q (fun i : Fin (n' + n + 1) => kcJoin p p' i) =
      ∏ k ∈ range (n' + n), q (kcJoin p p' (k + 1)) (kcJoin p p' k) :=
    kc_tup_prod (kcJoin p p') (n' + n) (fun a b => q b a)
  have e4 : ∏ k ∈ range (n' + n), q (kcJoin p p' (k + 1)) (kcJoin p p' k) =
      (∏ j ∈ range n', q (kcSeq p' j) (kcSeq p' (j + 1))) *
        ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    kc_join_prod p p' h0 (fun a b => q b a)
  rw [e1, e2, kc_join_prod p p' h0 q, e4] at hK
  have r1 : pathRatio q p = (∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1))) /
      ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) := by
    rw [← prod_div_distrib]; exact kc_prod p (fun a b => q a b / q b a)
  have r2 : pathRatio q p' = (∏ k ∈ range n', q (kcSeq p' k) (kcSeq p' (k + 1))) /
      ∏ k ∈ range n', q (kcSeq p' (k + 1)) (kcSeq p' k) := by
    rw [← prod_div_distrib]; exact kc_prod p' (fun a b => q a b / q b a)
  have hpos : 0 < ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    prod_pos fun k hk => (htw _ _).mp (kc_path_seq q p hp k (mem_range.mp hk))
  have hpos' : 0 < ∏ k ∈ range n', q (kcSeq p' (k + 1)) (kcSeq p' k) :=
    prod_pos fun k hk => (htw _ _).mp (kc_path_seq q p' hp' k (mem_range.mp hk))
  rw [r1, r2, div_eq_div_iff hpos.ne' hpos'.ne', mul_comm]
  exact hK

/-- The sequence `p₀, …, p_n, y`. -/
def kcSnoc {n : ℕ} (p : Fin (n + 1) → E) (y : E) (k : ℕ) : E :=
  if k ≤ n then kcSeq p k else y

/-- Invariance of the ratio products yields a positive solution of detailed balance:
`π(x)` is the ratio product along any path from a fixed state to `x`. -/
lemma kc_ri_rev (q : E → E → ℝ) (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q)
    (hirr : IsIrreducible q) (h : RatioInvariance q) : IsReversible q := by
  rcases isEmpty_or_nonempty E with hE | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ => 1, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  choose N P hP hP0 hPl using fun x => hirr x₀ x
  refine ⟨fun x => pathRatio q (P x), fun x => kc_ratio_pos q htw (P x) (hP x), fun x y => ?_⟩
  show pathRatio q (P x) * q x y = pathRatio q (P y) * q y x
  rcases (hq x y).lt_or_eq with hxy | hxy
  · have hyx : 0 < q y x := (htw x y).mp hxy
    have hS : ∀ k ≤ N x, kcSnoc (P x) y k = kcSeq (P x) k := fun k hk => if_pos hk
    have hSx : kcSnoc (P x) y (N x) = x := by rw [hS _ le_rfl, kcSeq_last, hPl]
    have hSy : kcSnoc (P x) y (N x + 1) = y := if_neg (by omega)
    have hpath : IsPath q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) := by
      refine kc_seq_path q _ _ fun k hk => ?_
      rcases Nat.lt_or_ge k (N x) with hk' | hk'
      · rw [hS k hk'.le, hS (k + 1) hk']
        exact kc_path_seq q (P x) (hP x) k hk'
      · have hkN : k = N x := by omega
        subst hkN
        rw [hSx, hSy]
        exact hxy
    have hratio : pathRatio q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) =
        pathRatio q (P x) * (q x y / q y x) := by
      have e : pathRatio q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) =
          ∏ k ∈ range (N x + 1), q (kcSnoc (P x) y k) (kcSnoc (P x) y (k + 1)) /
            q (kcSnoc (P x) y (k + 1)) (kcSnoc (P x) y k) :=
        kc_tup_prod (kcSnoc (P x) y) (N x + 1) (fun a b => q a b / q b a)
      have e' : pathRatio q (P x) =
          ∏ k ∈ range (N x), q (kcSeq (P x) k) (kcSeq (P x) (k + 1)) /
            q (kcSeq (P x) (k + 1)) (kcSeq (P x) k) :=
        kc_prod (P x) (fun a b => q a b / q b a)
      rw [e, e', prod_range_succ, hSx, hSy]
      congr 1
      refine prod_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [hS k hk'.le, hS (k + 1) hk']
    have hRI := h (N x + 1) (N y) (fun i => kcSnoc (P x) y i) (P y) hpath (hP y)
      (by
        show kcSnoc (P x) y ((0 : Fin (N x + 1 + 1)) : ℕ) = P y 0
        rw [Fin.val_zero, hS 0 (Nat.zero_le _), kcSeq_zero, hP0, hP0])
      (by
        show kcSnoc (P x) y ((Fin.last (N x + 1)) : ℕ) = P y (Fin.last (N y))
        rw [Fin.val_last, hSy, hPl])
    rw [hratio] at hRI
    rw [← hRI]
    field_simp
  · have hyx : q y x = 0 := by
      rcases (hq y x).lt_or_eq with h' | h'
      · exact absurd ((htw y x).mp h') (by rw [← hxy]; exact lt_irrefl 0)
      · exact h'.symm
    rw [← hxy, hyx, mul_zero, mul_zero]

/-- A reversible `q` has, for every base state, the normalized detailed-balance solution given
by the ratio products along paths from the base state. -/
lemma kc_rev_norm (q : E → E → ℝ) (htw : TwoWay q) (h : IsReversible q) (x₀ : E) :
    ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p := by
  obtain ⟨π, hπ, hdb⟩ := h
  refine ⟨fun x => π x / π x₀, fun x => div_pos (hπ x) (hπ x₀), div_self (hπ x₀).ne',
    fun x y => ?_, fun n p hp h0 => ?_⟩
  · show π x / π x₀ * q x y = π y / π x₀ * q y x
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hdb x y]
  · show π (p (Fin.last n)) / π x₀ = pathRatio q p
    have key : ∀ k ≤ n, π (kcSeq p k) = π (kcSeq p 0) *
        ∏ i ∈ range k, q (kcSeq p i) (kcSeq p (i + 1)) / q (kcSeq p (i + 1)) (kcSeq p i) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [prod_range_succ, ← mul_assoc, ← ih (by omega)]
        have hpos := kc_path_seq q p hp k (by omega)
        have hpos' := (htw _ _).mp hpos
        rw [← mul_div_assoc, hdb, mul_div_assoc, div_self hpos'.ne', mul_one]
    have e : pathRatio q p = ∏ i ∈ range n, q (kcSeq p i) (kcSeq p (i + 1)) /
        q (kcSeq p (i + 1)) (kcSeq p i) := kc_prod p (fun a b => q a b / q b a)
    rw [e, ← kcSeq_last p, key n le_rfl, kcSeq_zero, h0]
    field_simp [(hπ x₀).ne']

end SerfozoStochasticNetworks

open SerfozoStochasticNetworks

theorem solution {E : Type*} (q : E → E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hirr : IsIrreducible q) :
    (IsReversible q ↔ KolmogorovCriterion q) ∧ (IsReversible q ↔ RatioInvariance q) ∧
    (IsReversible q → ∀ x₀ : E, ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p) :=
  ⟨⟨kc_rev_kol q, fun h => kc_ri_rev q hq htw hirr (kc_kol_ri q htw h)⟩,
    ⟨fun h => kc_kol_ri q htw (kc_rev_kol q h), kc_ri_rev q hq htw hirr⟩,
    fun h x₀ => kc_rev_norm q htw h x₀⟩
