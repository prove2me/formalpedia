-- Prove2me | solution 1 for TSPHeuristics.NNLower.gbar_isTSPDist
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:13:06.792547+00:00
-- url     : https://prove2.me/submissions/789ff084-698a-4c3f-a4b7-088e450eaa3b

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

theorem aux_gb_append {E : List (ℕ × ℕ × ℝ)} {x y z : ℕ} {c d : ℝ}
    (h1 : WalkCost E x y c) (h2 : WalkCost E y z d) : WalkCost E x z (c + d) := by
  induction h1 with
  | nil x => simpa using h2
  | cons he h ih =>
    rw [add_assoc]
    exact WalkCost.cons he (ih h2)

theorem aux_gb_rev {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {c : ℝ}
    (h : WalkCost E x y c) : WalkCost E y x c := by
  induction h with
  | nil x => exact WalkCost.nil x
  | @cons x y z w c he h ih =>
    have h1 : WalkCost E y x (w + 0) := WalkCost.cons he.symm (WalkCost.nil x)
    rw [add_zero] at h1
    have := aux_gb_append ih h1
    rwa [add_comm] at this

theorem aux_gb_mono {E E' : List (ℕ × ℕ × ℝ)} (hE : ∀ e ∈ E, e ∈ E') {x y : ℕ} {c : ℝ}
    (h : WalkCost E x y c) : WalkCost E' x y c := by
  induction h with
  | nil x => exact WalkCost.nil x
  | cons he h ih => exact WalkCost.cons (he.imp (hE _) (hE _)) ih

theorem aux_gb_shift {E : List (ℕ × ℕ × ℝ)} (k : ℕ) {x y : ℕ} {c : ℝ}
    (h : WalkCost E x y c) :
    WalkCost (E.map (fun e => (e.1 + k, e.2.1 + k, e.2.2))) (x + k) (y + k) c := by
  induction h with
  | nil x => exact WalkCost.nil _
  | @cons x y z w c he h ih =>
    refine WalkCost.cons ?_ ih
    rcases he with he | he
    · left; exact List.mem_map.2 ⟨_, he, rfl⟩
    · right; exact List.mem_map.2 ⟨_, he, rfl⟩

theorem aux_gb_walk_nonneg {E : List (ℕ × ℕ × ℝ)} (hw : ∀ e ∈ E, 0 ≤ e.2.2) {x y : ℕ} {c : ℝ}
    (h : WalkCost E x y c) : 0 ≤ c := by
  induction h with
  | nil x => exact le_rfl
  | @cons x y z w c he h ih =>
    have : 0 ≤ w := by
      rcases he with he | he
      · exact hw _ he
      · exact hw _ he
    linarith

theorem aux_gb_ell_pos (i : ℕ) : 0 < ell i := by
  unfold ell
  have h2 : (1:ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> apply div_pos _ (by norm_num) <;> linarith

theorem aux_gb_ell_ge_one (i : ℕ) (hi : 1 ≤ i) : 1 ≤ ell i := by
  unfold ell
  have h2 : (2:ℝ) ≤ 2 ^ i := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi
  rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> rw [le_div_iff₀ (by norm_num)] <;>
    linarith

theorem aux_gb_F_nonneg : ∀ (i : ℕ), ∀ e ∈ edgesF i, 0 ≤ e.2.2
  | 0 => by simp [edgesF]
  | 1 => by
    intro e he
    simp only [edgesF, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  | i + 2 => by
    intro e he
    simp only [edgesF, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at he
    have hl := (aux_gb_ell_pos (i + 1)).le
    rcases he with (h | ⟨a, ha, rfl⟩) | rfl | rfl | rfl | rfl
    · exact aux_gb_F_nonneg (i + 1) e h
    · exact aux_gb_F_nonneg (i + 1) a ha
    · norm_num
    · norm_num
    · exact hl
    · exact hl

theorem aux_gb_numNodes (i : ℕ) :
    numNodes (i + 2) = 2 * numNodes (i + 1) + 1 ∧ 1 ≤ numNodes (i + 1) := by
  unfold numNodes
  have h1 : 1 ≤ 2 ^ (i + 2) := Nat.one_le_two_pow
  have h2 : 2 ^ (i + 2 + 1) = 2 * 2 ^ (i + 2) := by rw [pow_succ]; ring
  have h3 : 2 ^ (i + 1 + 1) = 2 ^ (i + 2) := rfl
  rw [h2, h3]
  constructor <;> omega

theorem aux_gb_conn : ∀ (i : ℕ), 1 ≤ i → ∀ x < numNodes i, ∃ c, WalkCost (edgesF i) 0 x c
  | 0, h => by omega
  | 1, _ => by
    intro x hx
    have h3 : numNodes 1 = 3 := by decide
    rw [h3] at hx
    interval_cases x
    · exact ⟨0, WalkCost.nil 0⟩
    · refine ⟨1 + 0, WalkCost.cons ?_ (WalkCost.nil 1)⟩
      left; simp [edgesF]
    · refine ⟨1 + 0, WalkCost.cons ?_ (WalkCost.nil 2)⟩
      left; simp [edgesF]
  | i + 2, _ => by
    intro x hx
    obtain ⟨hs, hs1⟩ := aux_gb_numNodes i
    set s := numNodes (i + 1) with hsdef
    have IH := aux_gb_conn (i + 1) (by omega)
    have hsub : ∀ e ∈ edgesF (i + 1), e ∈ edgesF (i + 2) := by
      intro e he
      simp only [edgesF, List.mem_append]
      exact Or.inl (Or.inl he)
    have hsubR : ∀ e ∈ (edgesF (i + 1)).map (fun e => (e.1 + (s + 1), e.2.1 + (s + 1), e.2.2)),
        e ∈ edgesF (i + 2) := by
      intro e he
      simp only [edgesF, List.mem_append]
      exact Or.inl (Or.inr he)
    have hCD : (s - 1, s, (1:ℝ)) ∈ edgesF (i + 2) := by
      simp only [edgesF, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl rfl)
    have hDE : (s, s + 1, (1:ℝ)) ∈ edgesF (i + 2) := by
      simp only [edgesF, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (Or.inl rfl))
    -- walk from 0 to s
    have hD : ∃ c, WalkCost (edgesF (i + 2)) 0 s c := by
      obtain ⟨c, hc⟩ := IH (s - 1) (by omega)
      have h1 : WalkCost (edgesF (i + 2)) (s - 1) s (1 + 0) :=
        WalkCost.cons (Or.inl hCD) (WalkCost.nil s)
      exact ⟨_, aux_gb_append (aux_gb_mono hsub hc) h1⟩
    rcases lt_trichotomy x s with hlt | heq | hgt
    · obtain ⟨c, hc⟩ := IH x hlt
      exact ⟨c, aux_gb_mono hsub hc⟩
    · subst heq; exact hD
    · obtain ⟨c0, hc0⟩ := hD
      have h1 : WalkCost (edgesF (i + 2)) s (s + 1) (1 + 0) :=
        WalkCost.cons (Or.inl hDE) (WalkCost.nil (s + 1))
      obtain ⟨y, rfl⟩ : ∃ y, x = y + (s + 1) := ⟨x - (s + 1), by omega⟩
      obtain ⟨c, hc⟩ := IH y (by omega)
      have h2 := aux_gb_mono hsubR (aux_gb_shift (s + 1) hc)
      rw [zero_add] at h2
      exact ⟨_, aux_gb_append (aux_gb_append hc0 h1) h2⟩

end TSPHeuristics.NNLower

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 1 ≤ i) : IsTSPDist (gbar i) := by
  have hnn : ∀ e ∈ edgesG i, 0 ≤ e.2.2 := by
    intro e he
    simp only [edgesG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | rfl | rfl
    · exact aux_gb_F_nonneg i e h
    · norm_num
    · have := aux_gb_ell_ge_one i hi
      simp only
      linarith
  have hsubG : ∀ e ∈ edgesF i, e ∈ edgesG i := by
    intro e he
    simp only [edgesG, List.mem_append]
    exact Or.inl he
  have hconn : ∀ a b : ℕ, a < numNodes i → b < numNodes i →
      ∃ c, WalkCost (edgesG i) a b c := by
    intro a b ha hb
    obtain ⟨c1, h1⟩ := aux_gb_conn i hi a ha
    obtain ⟨c2, h2⟩ := aux_gb_conn i hi b hb
    exact ⟨_, aux_gb_append (aux_gb_rev (aux_gb_mono hsubG h1)) (aux_gb_mono hsubG h2)⟩
  have hbdd : ∀ a b : ℕ, BddBelow {c : ℝ | WalkCost (edgesG i) a b c} :=
    fun a b => ⟨0, fun c hc => aux_gb_walk_nonneg hnn hc⟩
  have hnonneg : ∀ a b : ℕ, 0 ≤ spDist (edgesG i) a b :=
    fun a b => Real.sInf_nonneg (fun c hc => aux_gb_walk_nonneg hnn hc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    show spDist (edgesG i) a b = spDist (edgesG i) b a
    unfold spDist
    congr 1
    ext c
    exact ⟨aux_gb_rev, aux_gb_rev⟩
  · intro a b
    exact hnonneg a b
  · intro a b k
    show spDist (edgesG i) a k ≤ spDist (edgesG i) a b + spDist (edgesG i) b k
    obtain ⟨p0, hp0⟩ := hconn a b a.isLt b.isLt
    obtain ⟨q0, hq0⟩ := hconn b k b.isLt k.isLt
    have key : ∀ p q, WalkCost (edgesG i) a b p → WalkCost (edgesG i) b k q →
        spDist (edgesG i) a k ≤ p + q :=
      fun p q hp hq => csInf_le (hbdd a k) (aux_gb_append hp hq)
    have step1 : ∀ q, WalkCost (edgesG i) b k q →
        spDist (edgesG i) a k - q ≤ spDist (edgesG i) a b := by
      intro q hq
      apply le_csInf ⟨p0, hp0⟩
      intro p hp
      have := key p q hp hq
      linarith
    have step2 : spDist (edgesG i) a k - spDist (edgesG i) a b ≤ spDist (edgesG i) b k := by
      apply le_csInf ⟨q0, hq0⟩
      intro q hq
      have := step1 q hq
      linarith
    linarith
  · intro a
    show spDist (edgesG i) a a = 0
    exact le_antisymm (csInf_le (hbdd a a) (WalkCost.nil _)) (hnonneg a a)
