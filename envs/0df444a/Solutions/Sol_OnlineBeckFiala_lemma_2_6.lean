-- Prove2me | solution 1 for OnlineBeckFiala.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:12.112905+00:00
-- url     : https://prove2.me/submissions/9023bcd6-3590-4cce-85df-ed518018809e

import Mathlib

section
namespace OnlineBeckFiala

namespace Dev.L26

/-- the 12 admissible patterns: single nonzero entries and triples with sum ±1 -/
def pats : Fin 12 → (Fin 3 → SignType) :=
  ![![1,0,0],
   ![-1,0,0],
   ![0,1,0],
   ![0,-1,0],
   ![0,0,1],
   ![0,0,-1],
   ![1,1,-1],
   ![1,-1,1],
   ![1,-1,-1],
   ![-1,1,1],
   ![-1,1,-1],
   ![-1,-1,1]]

/-- counts (out of 12) of the coupling for the vertex type `(a,b,c)`, index `9a+3b+c` -/
def tbl : List (List ℕ) :=
  [[4,0,4,0,4,0,0,0,0,0,0,0],
   [4,0,4,0,0,4,0,0,0,0,0,0],
   [2,0,2,0,4,2,2,0,0,0,0,0],
   [4,0,0,4,4,0,0,0,0,0,0,0],
   [4,0,0,4,0,4,0,0,0,0,0,0],
   [2,0,0,2,2,4,0,2,0,0,0,0],
   [2,0,4,2,2,0,0,2,0,0,0,0],
   [2,0,2,4,0,2,2,0,0,0,0,0],
   [0,0,0,4,4,0,4,0,0,0,0,0],
   [0,4,4,0,4,0,0,0,0,0,0,0],
   [0,4,4,0,0,4,0,0,0,0,0,0],
   [0,2,2,0,2,4,0,0,0,2,0,0],
   [0,4,0,4,4,0,0,0,0,0,0,0],
   [0,4,0,4,0,4,0,0,0,0,0,0],
   [0,2,0,2,2,4,0,0,0,0,0,2],
   [0,2,2,4,2,0,0,0,0,2,0,0],
   [0,2,2,4,0,2,0,0,0,0,2,0],
   [0,0,0,4,0,4,0,0,0,4,0,0],
   [4,2,2,0,2,0,0,0,0,2,0,0],
   [2,4,2,0,0,2,2,0,0,0,0,0],
   [0,4,0,0,4,0,4,0,0,0,0,0],
   [2,4,0,2,2,0,0,2,0,0,0,0],
   [2,4,0,2,0,2,0,0,2,0,0,0],
   [0,4,0,0,0,4,0,4,0,0,0,0],
   [0,4,4,0,0,0,0,4,0,0,0,0],
   [0,4,0,4,0,0,4,0,0,0,0,0],
   [0,2,0,2,0,2,2,2,0,2,0,0]]

def cnt (a b c : Fin 3) (k : Fin 12) : ℕ := ((tbl.getD (9 * a.val + 3 * b.val + c.val) []).getD k.val 0)

def ea : Fin 3 → ℕ := ![4, 0, 4]
def eb : Fin 3 → ℕ := ![0, 4, 4]

theorem F2 : ∀ a b c : Fin 3, ∑ k, cnt a b c k = 12 := by decide +kernel

theorem F3 : ∀ a b c j : Fin 3,
    ∑ k, cnt a b c k * (if pats k j = 1 then 1 else 0) = ea (![a, b, c] j) := by decide +kernel

theorem F4 : ∀ a b c j : Fin 3,
    ∑ k, cnt a b c k * (if pats k j = -1 then 1 else 0) = eb (![a, b, c] j) := by decide +kernel

theorem F5 : ∀ a b c : Fin 3, ∀ k, cnt a b c k ≠ 0 →
    (∑ j, ((pats k j : SignType) : ℤ)) = 1 ∨ (∑ j, ((pats k j : SignType) : ℤ)) = -1 := by
  decide +kernel


noncomputable def w (a b : Fin 3 → ℝ) (j : Fin 3) : Fin 3 → ℝ :=
  ![1 - 3 * b j, 1 - 3 * a j, 3 * a j + 3 * b j - 1]

noncomputable def W (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) : ℝ := ∏ j, w a b j (t j)

noncomputable def gg (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) (k : Fin 12) : ℝ :=
  W a b t * (cnt (t 0) (t 1) (t 2) k : ℝ) / 12

theorem sum_w (a b : Fin 3 → ℝ) (j : Fin 3) : ∑ s, w a b j s = 1 := by
  simp [w, Fin.sum_univ_three]; ring

theorem w_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (j s : Fin 3) : 0 ≤ w a b j s := by
  have := ha1 j; have := hb1 j; have := hab j
  fin_cases s <;> simp [w] <;> linarith

theorem W_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (t : Fin 3 → Fin 3) : 0 ≤ W a b t :=
  Finset.prod_nonneg fun j _ => w_nonneg a b ha1 hb0 ha0 hb1 hab j (t j)

theorem marg (a b : Fin 3 → ℝ) (j0 : Fin 3) (h : Fin 3 → ℝ) :
    ∑ t : Fin 3 → Fin 3, W a b t * h (t j0) = ∑ s, w a b j0 s * h s := by
  have key := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3)))
    (fun i s => w a b i s * if i = j0 then h s else 1)
  rw [Fintype.piFinset_univ] at key
  have e1 : ∀ t : Fin 3 → Fin 3, (∏ i, (w a b i (t i) * if i = j0 then h (t i) else 1)) =
      W a b t * h (t j0) := by
    intro t
    rw [Finset.prod_mul_distrib]
    simp [W]
  simp only [e1] at key
  rw [← key]
  fin_cases j0 <;> simp [sum_w]

theorem sumW (a b : Fin 3 → ℝ) : ∑ t : Fin 3 → Fin 3, W a b t = 1 := by
  have := marg a b 0 (fun _ => 1)
  simpa [sum_w] using this

noncomputable def ff (a b : Fin 3 → ℝ) (δ : Fin 3 → SignType) : ℝ :=
  ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k = δ then 1 else 0)

theorem gg_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (t : Fin 3 → Fin 3) (k : Fin 12) : 0 ≤ gg a b t k := by
  unfold gg
  have := W_nonneg a b ha1 hb0 ha0 hb1 hab t
  positivity

open Classical in
theorem sumS (a b : Fin 3 → ℝ) (S : Set (Fin 3 → SignType)) :
    ∑ δ, S.indicator (ff a b) δ =
      ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k ∈ S then 1 else 0) := by
  have h1 : ∀ δ, S.indicator (ff a b) δ = ∑ t : Fin 3 → Fin 3, ∑ k,
      gg a b t k * (if pats k = δ then (if pats k ∈ S then 1 else 0) else 0) := by
    intro δ
    unfold ff
    simp only [Set.indicator]
    by_cases hδ : δ ∈ S
    · rw [if_pos hδ]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases e : pats k = δ <;> simp [e, hδ]
    · rw [if_neg hδ]
      symm
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases e : pats k = δ <;> simp [e, hδ]
  rw [Finset.sum_congr rfl fun δ _ => h1 δ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp

theorem sum_cnt (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) :
    ∑ k, gg a b t k = W a b t := by
  unfold gg
  have := F2 (t 0) (t 1) (t 2)
  have h : (∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ)) = 12 := by exact_mod_cast this
  rw [← Finset.sum_div, ← Finset.mul_sum, h]; ring


open Classical in
theorem margP (a b : Fin 3 → ℝ) (P : (Fin 3 → SignType) → Prop) (e : Fin 3 → ℕ) (j : Fin 3)
    (hP : ∀ x y z : Fin 3, ∑ k, cnt x y z k * (if P (pats k) then 1 else 0) = e (![x, y, z] j)) :
    ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k ∈ {δ | P δ} then 1 else 0) =
      ∑ s, w a b j s * ((e s : ℝ) / 12) := by
  rw [← marg a b j (fun s => (e s : ℝ) / 12)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h := hP (t 0) (t 1) (t 2)
  have h' : (∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ) * (if P (pats k) then 1 else 0)) = (e (t j) : ℝ) := by
    have : ![t 0, t 1, t 2] j = t j := by fin_cases j <;> rfl
    rw [this] at h
    exact_mod_cast h
  simp only [Set.mem_setOf_eq]
  unfold gg
  calc ∑ k, W a b t * (cnt (t 0) (t 1) (t 2) k : ℝ) / 12 * (if P (pats k) then 1 else 0)
      = W a b t / 12 * ∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ) * (if P (pats k) then 1 else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ = _ := by rw [h']; ring

end Dev.L26

open Classical in
theorem chk_lemma_2_6 (a b : Fin 3 → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) :
    ∃ p : PMF (Fin 3 → SignType),
      (∀ j, p.toOuterMeasure {δ | δ j = 1} = ENNReal.ofReal (a j) ∧
        p.toOuterMeasure {δ | δ j = -1} = ENNReal.ofReal (b j)) ∧
      ∀ δ ∈ p.support, (∑ j, (δ j : ℤ)) = 1 ∨ (∑ j, (δ j : ℤ)) = -1 := by
  have hgg := Dev.L26.gg_nonneg a b ha1 hb0 ha0 hb1 hab
  have hff : ∀ δ, 0 ≤ Dev.L26.ff a b δ := fun δ =>
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => by
      have := hgg t k; split_ifs <;> simp [this]
  have hsum : ∑ δ, Dev.L26.ff a b δ = 1 := by
    have := Dev.L26.sumS a b Set.univ
    simp only [Set.indicator_univ, Set.mem_univ, if_true, mul_one] at this
    rw [this]
    simp only [Dev.L26.sum_cnt]
    exact Dev.L26.sumW a b
  have hF : ∑ δ, ENNReal.ofReal (Dev.L26.ff a b δ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun δ _ => hff δ, hsum]; simp
  have hS : ∀ S : Set (Fin 3 → SignType),
      (PMF.ofFintype (fun δ => ENNReal.ofReal (Dev.L26.ff a b δ)) hF).toOuterMeasure S =
        ENNReal.ofReal (∑ t : Fin 3 → Fin 3, ∑ k, Dev.L26.gg a b t k *
          (if Dev.L26.pats k ∈ S then 1 else 0)) := by
    intro S
    rw [PMF.toOuterMeasure_apply_fintype, ← Dev.L26.sumS,
      ENNReal.ofReal_sum_of_nonneg fun δ _ => Set.indicator_nonneg (fun x _ => hff x) δ]
    refine Finset.sum_congr rfl fun δ _ => ?_
    by_cases hδ : δ ∈ S <;> simp [Set.indicator, hδ]
  refine ⟨PMF.ofFintype _ hF, fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [hS]
    congr 1
    rw [Dev.L26.margP a b (fun δ => δ j = 1) Dev.L26.ea j (fun x y z => by
      have := Dev.L26.F3 x y z j; simpa using this)]
    fin_cases j <;> simp [Dev.L26.w, Dev.L26.ea, Fin.sum_univ_three] <;> ring
  · rw [hS]
    congr 1
    rw [Dev.L26.margP a b (fun δ => δ j = -1) Dev.L26.eb j (fun x y z => by
      have := Dev.L26.F4 x y z j; simpa using this)]
    fin_cases j <;> simp [Dev.L26.w, Dev.L26.eb, Fin.sum_univ_three] <;> ring
  · intro δ hδ
    rw [PMF.mem_support_iff, PMF.ofFintype_apply] at hδ
    have hpos : 0 < Dev.L26.ff a b δ := by
      rcases (hff δ).lt_or_eq with h | h
      · exact h
      · exfalso; apply hδ; rw [← h]; simp
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have e : Dev.L26.pats k = δ := by
      by_contra hne; simp [hne] at hk
    have hc : Dev.L26.cnt (t 0) (t 1) (t 2) k ≠ 0 := by
      intro h0; simp [Dev.L26.gg, h0] at hk
    subst e
    exact Dev.L26.F5 _ _ _ k hc

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_lemma_2_6 := @OnlineBeckFiala.chk_lemma_2_6
