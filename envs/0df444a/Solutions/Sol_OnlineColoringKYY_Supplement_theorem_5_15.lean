-- Prove2me | solution 1 for OnlineColoringKYY.Supplement.theorem_5_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T15:50:12.132746+00:00
-- url     : https://prove2.me/submissions/f7fed5cc-955d-461b-8454-ed7e16f69bd7

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_dLevel

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-!
Blueprint for Theorem 5.15 (Algorithm 2, the `d`-level algorithm), q414.
Every lemma below is a stub (`sorry`) proved in a Part file; `chk_theorem_5_15` is proved from them.

A coloring is `c : List ℕ` (colors of vertices `0, …, len − 1` in arrival order). For a level `t`
(`2 ≤ t ≤ d − 1`): `Bset c t` = last (`t`-th) vertices of the colors used exactly `t` times, `Aset c t` =
their `(t−1)`-th vertices; `partner c t a` = the `b ∈ Bset` of the color of `a`; `grp p a` = the
vertices `≤ a` of the color of `a`; `Eset … col a` = vertices of `B` of base color `col` non-adjacent
to `grp a`; `rank` = paper's backward rank (Definition 5.8); `beta`/`tau` decode the profile
(paper's proof of Lemma 5.10): the target color of `b` is a function of the prefix before `b`.
-/
def Traj (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c : List ℕ) : Prop :=
  c.length ≤ n ∧ ∀ u (hn : u < n), u < c.length →
    c.getD u 0 ∈ (dLevelStep d θ G ⟨u, hn⟩ (c.take u)).support

noncomputable def lvl (c : List ℕ) (j : ℕ) : ℕ := (c.toFinset.filter (fun x => c.count x = j)).card

def adjN {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩

def phiN {n k : ℕ} {G : SimpleGraph (Fin n)} (C : G.Coloring (Fin k)) (a : ℕ) : ℕ :=
  if h : a < n then (C ⟨a, h⟩).val else 0

/-- 1-based occurrence index of position `u` within its color. -/
def occ (c : List ℕ) (u : ℕ) : ℕ := (c.take u).count (c.getD u 0) + 1

noncomputable def Bset (c : List ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range c.length).filter (fun b => c.count (c.getD b 0) = t ∧ occ c b = t)

noncomputable def Aset (c : List ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range c.length).filter (fun a => c.count (c.getD a 0) = t ∧ occ c a = t - 1)

noncomputable def grp (p : List ℕ) (a : ℕ) : Finset ℕ :=
  (Finset.range (a + 1)).filter (fun u => p.getD u 0 = p.getD a 0)

noncomputable def Eset {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (p : List ℕ) (B : Finset ℕ)
    (col a : ℕ) : Finset ℕ :=
  B.filter (fun b => φ b = col ∧ ∀ u ∈ grp p a, ¬ adjN G u b)

noncomputable def beta {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (p : List ℕ) (B : Finset ℕ)
    (col r a : ℕ) : ℕ :=
  ((Eset G φ p B col a).filter
    (fun b => ((Eset G φ p B col a).filter (fun b' => b < b')).card = r)).sup id

noncomputable def tau {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (B A : Finset ℕ)
    (col r : ℕ → ℕ) (b : ℕ) (p : List ℕ) : ℕ :=
  if h : (A.filter (fun a => a < b ∧ beta G φ p B (col a) (r a) a = b)).Nonempty then
    p.getD ((A.filter (fun a => a < b ∧ beta G φ p B (col a) (r a) a = b)).min' h) 0
  else 0

/-- The event that every `b ∈ B` takes the target color `τ b (prefix)`, which had count `s` then. -/
def EvT (s : ℕ) (B : Finset ℕ) (τ : ℕ → List ℕ → ℕ) (c : List ℕ) : Prop :=
  ∀ b ∈ B, b < c.length →
    (c.take b).count (τ b (c.take b)) = s ∧ c.getD b 0 = τ b (c.take b)

noncomputable def partner (c : List ℕ) (t a : ℕ) : ℕ :=
  ((Bset c t).filter (fun b => c.getD b 0 = c.getD a 0)).sup id

noncomputable def rank {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (c : List ℕ) (t a : ℕ) : ℕ :=
  ((Eset G φ c (Bset c t) (φ (partner c t a)) a).filter (fun b' => partner c t a < b')).card

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartS1
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
/-! ### Basic list facts -/
lemma lt_freshColor (c : List ℕ) (x : ℕ) (hx : x ∈ c) : x < freshColor c := by
  induction c with
  | nil => simp at hx
  | cons a l ih =>
    simp only [freshColor, List.foldr_cons] at *
    rcases List.mem_cons.mp hx with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

end OnlineColoringKYY.Supplement.Dev.T515.PartS1
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
/-! ### run_support -/
theorem run_support (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (m : ℕ) (h : m ≤ n) (c : List ℕ) (hc : c ∈ (dLevelRun d θ G m h).support) :
    c.length = m ∧ Traj d θ G c := by
  induction m generalizing c with
  | zero =>
    simp only [dLevelRun, PMF.support_pure, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨rfl, Nat.zero_le _, fun u _ hu => absurd hu (by simp)⟩
  | succ m ih =>
    simp only [dLevelRun, PMF.mem_support_bind_iff, PMF.support_map,
      Set.mem_image] at hc
    obtain ⟨c0, hc0, x, hx, rfl⟩ := hc
    obtain ⟨hlen, -, htr⟩ := ih (Nat.le_of_succ_le h) c0 hc0
    refine ⟨by simp [hlen], by simp [hlen]; omega, fun u hn hu => ?_⟩
    simp only [List.length_append, List.length_singleton] at hu
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : u < m + 1) with hum | rfl
    · rw [List.getD_append _ _ _ _ (by omega), List.take_append_of_le_length (by omega)]
      exact htr u hn (by omega)
    · subst hlen
      rw [List.getD_append_right _ _ _ _ le_rfl, List.take_left' rfl]
      simpa using hx

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part A: support and deterministic counting -/
alias run_support := OnlineColoringKYY.Supplement.Dev.T515.PartA.run_support

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartS1
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
lemma freshColor_not_mem (c : List ℕ) : freshColor c ∉ c := fun h =>
  lt_irrefl _ (lt_freshColor c _ h)

lemma getD_take_of_lt (c : List ℕ) (j i : ℕ) (h : i < j) :
    (c.take j).getD i 0 = c.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_mem_take (c : List ℕ) (j u : ℕ) (h : u < j) (hu : u < c.length) :
    c.getD u 0 ∈ c.take j := by
  rw [← getD_take_of_lt c j u h, List.getD_eq_getElem _ _ (by simp; omega)]
  exact List.getElem_mem _

lemma getD_mem (c : List ℕ) (u : ℕ) (hu : u < c.length) : c.getD u 0 ∈ c := by
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem _

/-- `count` of a one-longer prefix. -/
lemma count_take_succ (c : List ℕ) (u x : ℕ) :
    (c.take (u + 1)).count x =
      (c.take u).count x + if u < c.length ∧ c.getD u 0 = x then 1 else 0 := by
  by_cases hu : u < c.length
  · rw [List.take_add_one, List.getElem?_eq_getElem hu, Option.toList_some, List.count_append,
      List.count_singleton]
    rw [← List.getD_eq_getElem _ 0 hu]
    by_cases hx : c.getD u 0 = x
    · simp only [hx, hu, and_self, beq_self_eq_true, if_true]
    · have hb : (c.getD u 0 == x) = false := by simpa using hx
      simp only [hb, hx, and_false, if_false, Bool.false_eq_true]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp [hu]

lemma count_take_mono (c : List ℕ) (x : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (c.take j).count x ≤ (c.take j').count x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, count_take_succ]
    have := ih (by omega)
    omega

/-- Intermediate values of the prefix count are attained at a position of color `x`. -/
lemma exists_pos_count_take (c : List ℕ) (x j : ℕ) :
    ∀ u, j < (c.take u).count x →
      ∃ v, v < u ∧ v < c.length ∧ c.getD v 0 = x ∧ (c.take v).count x = j := by
  intro u
  induction u with
  | zero => simp
  | succ u ih =>
    intro hj
    rw [count_take_succ] at hj
    by_cases hlt : j < (c.take u).count x
    · obtain ⟨v, h1, h2⟩ := ih hlt
      exact ⟨v, by omega, h2⟩
    · split_ifs at hj with hu
      · exact ⟨u, by omega, hu.1, hu.2, by omega⟩
      · omega

/-! ### Occurrence index -/
lemma occ_lt (c : List ℕ) (u1 u2 : ℕ) (h : u1 < u2) (hu1 : u1 < c.length)
    (he : c.getD u1 0 = c.getD u2 0) : occ c u1 < occ c u2 := by
  unfold occ
  rw [← he]
  have h1 := count_take_succ c u1 (c.getD u1 0)
  rw [if_pos ⟨hu1, rfl⟩] at h1
  have h2 := count_take_mono c (c.getD u1 0) (show u1 + 1 ≤ u2 by omega)
  omega

lemma pos_eq_of_occ (c : List ℕ) (u1 u2 : ℕ) (hu1 : u1 < c.length) (hu2 : u2 < c.length)
    (he : c.getD u1 0 = c.getD u2 0) (ho : occ c u1 = occ c u2) : u1 = u2 := by
  rcases lt_trichotomy u1 u2 with h | h | h
  · have := occ_lt c u1 u2 h hu1 he; omega
  · exact h
  · have := occ_lt c u2 u1 h hu2 he.symm; omega

lemma exists_occ (c : List ℕ) (x j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ c.count x) :
    ∃ v, v < c.length ∧ c.getD v 0 = x ∧ occ c v = j := by
  obtain ⟨v, -, hv, hx, hc⟩ := exists_pos_count_take c x (j - 1) c.length
    (by rw [List.take_of_length_le le_rfl]; omega)
  exact ⟨v, hv, hx, by unfold occ; rw [hx, hc]; omega⟩

lemma mem_Bset (c : List ℕ) (t b : ℕ) :
    b ∈ Bset c t ↔ b < c.length ∧ c.count (c.getD b 0) = t ∧ occ c b = t := by
  simp [Bset]

lemma mem_Aset (c : List ℕ) (t a : ℕ) :
    a ∈ Aset c t ↔ a < c.length ∧ c.count (c.getD a 0) = t ∧ occ c a = t - 1 := by
  simp [Aset]

/-- Positions of the `j`-th occurrences of the level-`t` colors are as many as those colors. -/
lemma card_occ_eq (c : List ℕ) (t j : ℕ) (hj1 : 1 ≤ j) (hjt : j ≤ t) :
    ((Finset.range c.length).filter
      (fun b => c.count (c.getD b 0) = t ∧ occ c b = j)).card = lvl c t := by
  unfold lvl
  apply Finset.card_bij (fun b _ => c.getD b 0)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset] at hb ⊢
    exact ⟨getD_mem c b hb.1, hb.2.1⟩
  · intro b1 h1 b2 h2 he
    simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
    exact pos_eq_of_occ c b1 b2 h1.1 h2.1 he (by omega)
  · intro x hx
    simp only [Finset.mem_filter, List.mem_toFinset] at hx
    obtain ⟨v, hv, hvx, ho⟩ := exists_occ c x j hj1 (by omega)
    exact ⟨v, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hv, by rw [hvx]; exact hx.2, ho⟩, hvx⟩

lemma card_Bset (c : List ℕ) (t : ℕ) (ht : 1 ≤ t) : (Bset c t).card = lvl c t :=
  card_occ_eq c t t ht le_rfl

lemma card_Aset (c : List ℕ) (t : ℕ) (ht : 2 ≤ t) : (Aset c t).card = lvl c t :=
  card_occ_eq c t (t - 1) (by omega) (by omega)

/-! ### Partner -/
lemma partner_eq (c : List ℕ) (t a b : ℕ) (hb : b ∈ Bset c t)
    (he : c.getD b 0 = c.getD a 0) : partner c t a = b := by
  unfold partner
  have : (Bset c t).filter (fun b' => c.getD b' 0 = c.getD a 0) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', he'⟩
      have hb1 := (mem_Bset c t b).1 hb
      have hb2 := (mem_Bset c t b').1 hb'
      exact pos_eq_of_occ c b' b hb2.1 hb1.1 (by rw [he', he]) (by omega)
    · rintro rfl; exact ⟨hb, he⟩
  rw [this, Finset.sup_singleton]; rfl

lemma partner_spec (c : List ℕ) (t : ℕ) (ht : 2 ≤ t) (a : ℕ) (ha : a ∈ Aset c t) :
    partner c t a ∈ Bset c t ∧ c.getD (partner c t a) 0 = c.getD a 0 ∧ a < partner c t a := by
  have ha' := (mem_Aset c t a).1 ha
  obtain ⟨b, hb, hbx, ho⟩ := exists_occ c (c.getD a 0) t (by omega) (by omega)
  have hbB : b ∈ Bset c t := (mem_Bset c t b).2 ⟨hb, by rw [hbx]; exact ha'.2.1, ho⟩
  rw [partner_eq c t a b hbB hbx]
  refine ⟨hbB, hbx, ?_⟩
  by_contra hle
  rcases (not_lt.1 hle).lt_or_eq with h | h
  · have := occ_lt c b a h hb hbx; omega
  · subst h; omega

/-! ### Support of one step of Algorithm 2 -/
/-- The qualifying test of level `i` in `dLevelStep`. -/
def LvOK (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (c' : List ℕ) (i : ℕ) :
    Prop :=
  (eligibleLevel G v c' i).Nonempty ∧ θ i ≤ (eligibleLevel G v c' i).card

/-- Step-support case analysis: either the fresh color (no level qualifies), or an eligible color
of the largest qualifying level `i`. -/
lemma step_support (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c' : List ℕ) (x : ℕ) (hx : x ∈ (dLevelStep d θ G v c').support) :
    (x = freshColor c' ∧ x ∉ c' ∧ ∀ i, 1 ≤ i → i ≤ d - 1 → ¬ LvOK θ G v c' i) ∨
      (∃ i, 1 ≤ i ∧ i ≤ d - 1 ∧ x ∈ eligibleLevel G v c' i ∧ LvOK θ G v c' i ∧
        ∀ j, i < j → j ≤ d - 1 → ¬ LvOK θ G v c' j) := by
  unfold dLevelStep at hx
  simp only at hx
  split_ifs at hx with h
  · rw [PMF.mem_support_uniformOfFinset_iff] at hx
    have hm := Finset.mem_filter.1 (Finset.max'_mem _ h)
    refine Or.inr ⟨_, (Finset.mem_Icc.1 hm.1).1, (Finset.mem_Icc.1 hm.1).2, hx, hm.2,
      fun j hj hjd hjt => ?_⟩
    have hj' : j ∈ (Finset.Icc 1 (d - 1)).filter (fun i => (eligibleLevel G v c' i).Nonempty ∧
        θ i ≤ (eligibleLevel G v c' i).card) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hm.1).1; omega, hjd⟩,
        hjt⟩
    have := Finset.le_max' _ j hj'
    omega
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact Or.inl ⟨rfl, freshColor_not_mem c', fun i h1 h2 hi =>
      h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, hi⟩⟩⟩

lemma mem_eligibleLevel {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (c' : List ℕ) (i x : ℕ) :
    x ∈ eligibleLevel G v c' i ↔ x ∈ c' ∧ c'.count x = i ∧ Eligible G v c' x := by
  simp [eligibleLevel]

/-- A non-fresh color chosen by the step is eligible. -/
lemma eligible_of_step (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c' : List ℕ) (x : ℕ) (hx : x ∈ (dLevelStep d θ G v c').support) (hmem : x ∈ c') :
    Eligible G v c' x := by
  rcases step_support d θ G v c' x hx with h | ⟨i, -, -, hi, -⟩
  · exact absurd hmem h.2.1
  · exact ((mem_eligibleLevel G v c' i x).1 hi).2.2

/-! ### Trajectory helpers -/
lemma traj_lt_n {d : ℕ} {θ : ℕ → ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) {u : ℕ} (hu : u < c.length) : u < n :=
  lt_of_lt_of_le hu hc.1

lemma traj_step {d : ℕ} {θ : ℕ → ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) (u : ℕ) (hu : u < c.length) :
    c.getD u 0 ∈ (dLevelStep d θ G ⟨u, traj_lt_n hc hu⟩ (c.take u)).support :=
  hc.2 u _ hu

end OnlineColoringKYY.Supplement.Dev.T515.PartS1
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
/-! ### count_le_d -/
lemma prefix_count_le (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) (u : ℕ) (hu : u < c.length) :
    (c.take u).count (c.getD u 0) ≤ d - 1 := by
  rcases step_support d θ G _ _ _ (traj_step hc u hu) with h | ⟨i, -, hi, hx, -⟩
  · rw [List.count_eq_zero_of_not_mem h.2.1]; omega
  · rw [((mem_eligibleLevel G _ _ i _).1 hx).2.1]; exact hi

theorem count_le_d (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c : List ℕ) (hc : Traj d θ G c) (x : ℕ) : c.count x ≤ d := by
  have key : ∀ j, (c.take j).count x ≤ d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [count_take_succ]
      split_ifs with hj
      · have := prefix_count_le d θ hc j hj.1
        rw [hj.2] at this
        omega
      · omega
  simpa using key c.length

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias count_le_d := OnlineColoringKYY.Supplement.Dev.T515.PartA.count_le_d

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
/-! ### card_toFinset_eq -/
theorem card_toFinset_eq (d : ℕ) (c : List ℕ) (hc : ∀ x, c.count x ≤ d) :
    d * c.toFinset.card = c.length + ∑ t ∈ Finset.range d, (d - t) * lvl c t := by
  have h1 : d * c.toFinset.card = ∑ x ∈ c.toFinset, (c.count x + (d - c.count x)) := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have := hc x
    omega
  have h2 : ∑ x ∈ c.toFinset, (d - c.count x) =
      ∑ t ∈ Finset.range (d + 1), (d - t) * lvl c t := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := c.toFinset) (t := Finset.range (d + 1))
      (g := fun x => c.count x) (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hc x)))]
    apply Finset.sum_congr rfl
    intro t _
    unfold lvl
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, mul_one]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [h1, Finset.sum_add_distrib, List.sum_toFinset_count_eq_length, h2,
    Finset.sum_range_succ, Nat.sub_self, zero_mul, add_zero]

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias card_toFinset_eq := OnlineColoringKYY.Supplement.Dev.T515.PartA.card_toFinset_eq

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
/-! ### lvl_one_le -/
/-- Count as the number of positions. -/
lemma count_eq_card_pos (c : List ℕ) (x : ℕ) :
    c.count x = ((Finset.range c.length).filter (fun i => c.getD i 0 = x)).card := by
  induction c using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.count_append, ih, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hfl : (Finset.range l.length).filter (fun i => (l ++ [a]).getD i 0 = x) =
        (Finset.range l.length).filter (fun i => l.getD i 0 = x) := by
      apply Finset.filter_congr
      intro i hi
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
    have hl : (l ++ [a]).getD l.length 0 = a := by
      rw [List.getD_append_right _ _ _ _ le_rfl]; simp
    rw [hfl, hl]
    by_cases hax : a = x
    · subst hax
      rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      simp
    · rw [if_neg hax]
      simpa [List.count_singleton] using hax

lemma pos_unique (c : List ℕ) (x : ℕ) (hx : c.count x = 1) (u1 u2 : ℕ) (h1 : u1 < c.length)
    (h2 : u2 < c.length) (e1 : c.getD u1 0 = x) (e2 : c.getD u2 0 = x) : u1 = u2 := by
  rw [count_eq_card_pos] at hx
  exact Finset.card_le_one.mp hx.le u1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, e1⟩) u2
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, e2⟩)

lemma exists_pos_of_mem (c : List ℕ) (x : ℕ) (hx : x ∈ c) :
    ∃ u, u < c.length ∧ c.getD u 0 = x := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, he]⟩

lemma phiN_ne_of_adjN {n k : ℕ} {G : SimpleGraph (Fin n)} (C : G.Coloring (Fin k)) (u v : ℕ)
    (h : adjN G u v) : phiN C u ≠ phiN C v := by
  obtain ⟨hu, hv, hadj⟩ := h
  unfold phiN
  rw [dif_pos hu, dif_pos hv]
  intro he
  exact C.valid hadj (Fin.ext he)

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartS1
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
lemma prefixAdj_of_adjN {n : ℕ} (G : SimpleGraph (Fin n)) (u v : ℕ) (hv : v < n)
    (huv : u < v) (h : adjN G u v) : prefixAdj G ⟨v, hv⟩ u v := by
  obtain ⟨hu, hv', hadj⟩ := h
  exact ⟨by simp; omega, by simp, hadj⟩

lemma adjN_of_prefixAdj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : ℕ) (hv : v < n)
    (h : prefixAdj G ⟨v, hv⟩ u v) : adjN G u v := by
  obtain ⟨hu, hv', hadj⟩ := h
  exact ⟨by simp at hu; omega, hv, hadj⟩

end OnlineColoringKYY.Supplement.Dev.T515.PartS1
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
lemma fiber_le (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ) (hθ1 : 1 ≤ θ 1) {n k : ℕ}
    (G : SimpleGraph (Fin n)) (C : G.Coloring (Fin k)) (c : List ℕ) (hc : Traj d θ G c) (i : ℕ) :
    (((Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1)).filter
      (fun u => phiN C u = i)).card ≤ θ 1 := by
  set F := ((Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1)).filter
      (fun u => phiN C u = i) with hF
  have memF : ∀ u, u ∈ F ↔ u < c.length ∧ c.count (c.getD u 0) = 1 ∧ phiN C u = i := by
    intro u; simp [hF, and_assoc]
  by_contra hlt
  rw [not_le] at hlt
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  set w := F.max' hne with hw
  have hwF : w ∈ F := F.max'_mem hne
  obtain ⟨hwl, hwc, hwi⟩ := (memF w).mp hwF
  have hwn : w < n := traj_lt_n hc hwl
  set E1 := eligibleLevel G ⟨w, hwn⟩ (c.take w) 1 with hE1
  have hsub : (F.erase w).image (fun u => c.getD u 0) ⊆ E1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨huw, huF⟩ := Finset.mem_erase.mp hu
    obtain ⟨hul, huc, hui⟩ := (memF u).mp huF
    have hlt : u < w := lt_of_le_of_ne (F.le_max' u huF) huw
    have hmem := getD_mem_take c w u hlt hul
    rw [hE1, mem_eligibleLevel]
    refine ⟨hmem, ?_, ?_⟩
    · have h1 := (List.take_sublist w c).count_le (c.getD u 0)
      have h2 := List.count_pos_iff.mpr hmem
      omega
    · intro u' hu' hadj he
      rw [getD_take_of_lt c w u' hu'] at he
      have hu'w : u' < w := hu'
      have hu'l : u' < c.length := by omega
      have := pos_unique c _ huc u' u hu'l hul he rfl
      subst this
      exact phiN_ne_of_adjN C u' w (adjN_of_prefixAdj G u' w hwn hadj) (by rw [hui, hwi])
  have hinj : Set.InjOn (fun u => c.getD u 0) (F.erase w : Set ℕ) := by
    intro u1 h1 u2 h2 he
    obtain ⟨h1l, h1c, -⟩ := (memF u1).mp (Finset.mem_of_mem_erase h1)
    obtain ⟨h2l, -, -⟩ := (memF u2).mp (Finset.mem_of_mem_erase h2)
    exact pos_unique c _ h1c u1 u2 h1l h2l rfl he.symm
  have hcardE : θ 1 ≤ E1.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hwF] at this
    omega
  rcases step_support d θ G _ _ _ (traj_step hc w hwl) with h | ⟨j, -, -, hx, -⟩
  · exact h.2.2 1 le_rfl (by omega)
      ⟨Finset.card_pos.mp (lt_of_lt_of_le hθ1 hcardE), hcardE⟩
  · have hmem := ((mem_eligibleLevel G _ _ j _).1 hx).1
    obtain ⟨u, hu, hue⟩ := exists_pos_of_mem _ _ hmem
    rw [List.length_take] at hu
    have hu' : u < w := lt_of_lt_of_le hu (min_le_left _ _)
    rw [getD_take_of_lt c w u hu'] at hue
    have := pos_unique c _ hwc u w (by omega) hwl hue rfl
    omega

/-- Paper's Lemma 5.6. -/
theorem lvl_one_le (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ) (hθ1 : 1 ≤ θ 1) {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.Colorable k) (c : List ℕ) (hc : Traj d θ G c) :
    lvl c 1 ≤ k * θ 1 := by
  obtain ⟨C⟩ := hG
  set V1 := (Finset.range c.length).filter (fun u => c.count (c.getD u 0) = 1) with hV1
  have h1 : lvl c 1 ≤ V1.card := by
    unfold lvl
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun u => c.getD u 0))
    intro x hx
    simp only [Finset.mem_filter, List.mem_toFinset] at hx
    obtain ⟨u, hu, rfl⟩ := exists_pos_of_mem c x hx.1
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hx.2⟩, rfl⟩
  have h2 : V1.card = ∑ i ∈ Finset.range k, (V1.filter (fun u => phiN C u = i)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro u hu
    have hu' : u < c.length := by simp [hV1] at hu; exact hu.1
    have hun : u < n := traj_lt_n hc hu'
    simp only [Finset.coe_range, Set.mem_Iio, phiN, dif_pos hun]
    exact (C ⟨u, hun⟩).isLt
  have h3 : ∑ i ∈ Finset.range k, (V1.filter (fun u => phiN C u = i)).card ≤
      ∑ _i ∈ Finset.range k, θ 1 :=
    Finset.sum_le_sum (fun i _ => fiber_le d hd θ hθ1 G C c hc i)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h3
  omega

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias lvl_one_le := OnlineColoringKYY.Supplement.Dev.T515.PartA.lvl_one_le

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartA
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
/-! ### expColors_le_n -/
theorem expColors_le_n (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    expColors (dLevelRun d θ G n le_rfl) ≤ n := by
  unfold expColors
  calc ∑' c, dLevelRun d θ G n le_rfl c * (c.toFinset.card : ENNReal)
      ≤ ∑' c, dLevelRun d θ G n le_rfl c * (n : ENNReal) := by
        refine ENNReal.tsum_le_tsum (fun c => ?_)
        by_cases hμ : dLevelRun d θ G n le_rfl c = 0
        · simp [hμ]
        have hlen := (run_support d θ G n le_rfl c ((PMF.mem_support_iff _ _).2 hμ)).1
        gcongr
        exact_mod_cast (List.toFinset_card_le c).trans hlen.le
    _ = n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end OnlineColoringKYY.Supplement.Dev.T515.PartA
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias expColors_le_n := OnlineColoringKYY.Supplement.Dev.T515.PartA.expColors_le_n

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartS1
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
/-- In a trajectory, a vertex whose color was already used is not adjacent to any earlier vertex
of that color. -/
lemma traj_not_adj {d : ℕ} {θ : ℕ → ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) (b : ℕ) (hb : b < c.length) (hpos : 1 ≤ (c.take b).count (c.getD b 0))
    (u : ℕ) (hub : u < b) (he : c.getD u 0 = c.getD b 0) : ¬ adjN G u b := by
  intro hadj
  have hmem : c.getD b 0 ∈ c.take b := List.count_pos_iff.1 hpos
  have hel := eligible_of_step d θ G _ _ _ (traj_step hc b hb) hmem
  exact hel u hub (prefixAdj_of_adjN G u b (traj_lt_n hc hb) hub hadj)
    (by rw [getD_take_of_lt c b u hub, he])

/-! ### Eset, beta -/
lemma grp_take (c : List ℕ) (b a : ℕ) (h : a < b) : grp (c.take b) a = grp c a := by
  unfold grp
  apply Finset.filter_congr
  intro u hu
  simp only [Finset.mem_range] at hu
  rw [getD_take_of_lt c b u (by omega), getD_take_of_lt c b a h]

lemma Eset_take {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (c : List ℕ) (B : Finset ℕ)
    (col b a : ℕ) (h : a < b) : Eset G φ (c.take b) B col a = Eset G φ c B col a := by
  unfold Eset; rw [grp_take c b a h]

lemma beta_take {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (c : List ℕ) (B : Finset ℕ)
    (col r b a : ℕ) (h : a < b) : beta G φ (c.take b) B col r a = beta G φ c B col r a := by
  unfold beta; rw [Eset_take G φ c B col b a h]

/-- In a finite set, an element is determined by the number of larger elements. -/
lemma sup_filter_rank (E : Finset ℕ) (b : ℕ) (hb : b ∈ E) :
    (E.filter (fun b'' => (E.filter (fun b' => b'' < b')).card =
      (E.filter (fun b' => b < b')).card)).sup id = b := by
  have key : ∀ x y, x ∈ E → y ∈ E → x < y →
      (E.filter (fun b' => y < b')).card < (E.filter (fun b' => x < b')).card := by
    intro x y _ hy hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨y, Finset.mem_filter.2 ⟨hy, hxy⟩, by simp⟩
    · intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, by omega⟩
  have : E.filter (fun b'' => (E.filter (fun b' => b'' < b')).card =
      (E.filter (fun b' => b < b')).card) = {b} := by
    ext b''
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb'', hc⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := key b'' b hb'' hb h; omega
      · have := key b b'' hb hb'' h; omega
    · rintro rfl; exact ⟨hb, rfl⟩
  rw [this, Finset.sup_singleton]; rfl

lemma beta_eq {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (p : List ℕ) (B : Finset ℕ)
    (col a b : ℕ) (hb : b ∈ Eset G φ p B col a) :
    beta G φ p B col ((Eset G φ p B col a).filter (fun b' => b < b')).card a = b :=
  sup_filter_rank _ b hb

/-! ### The profile -/
lemma Bset_count_take (c : List ℕ) (t b : ℕ) (hb : b ∈ Bset c t) :
    (c.take b).count (c.getD b 0) = t - 1 := by
  have h := ((mem_Bset c t b).1 hb).2.2
  unfold occ at h
  omega

/-- The partner of `a ∈ Aset` lies in its own `Eset` (it is not adjacent to the group of `a`). -/
lemma partner_mem_Eset {d : ℕ} {θ : ℕ → ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) (φ : ℕ → ℕ) (t : ℕ) (ht : 2 ≤ t) (a : ℕ) (ha : a ∈ Aset c t) :
    partner c t a ∈ Eset G φ c (Bset c t) (φ (partner c t a)) a := by
  obtain ⟨hpB, hpe, hap⟩ := partner_spec c t ht a ha
  have hpl := ((mem_Bset c t _).1 hpB).1
  have hcnt := Bset_count_take c t _ hpB
  simp only [Eset, Finset.mem_filter]
  refine ⟨hpB, trivial, fun u hu => ?_⟩
  simp only [grp, Finset.mem_filter, Finset.mem_range] at hu
  exact traj_not_adj hc _ hpl (by omega) u (by omega) (by rw [hu.2, hpe])

lemma beta_partner {d : ℕ} {θ : ℕ → ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {c : List ℕ}
    (hc : Traj d θ G c) (φ : ℕ → ℕ) (t : ℕ) (ht : 2 ≤ t) (a : ℕ) (ha : a ∈ Aset c t) :
    beta G φ c (Bset c t) (φ (partner c t a)) (rank G φ c t a) a = partner c t a :=
  beta_eq G φ c _ _ a _ (partner_mem_Eset hc φ t ht a ha)

theorem profile_basic (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ)
    (hθ : ∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.Coloring (Fin k)) (t : ℕ) (ht2 : 2 ≤ t) (htd : t ≤ d - 1) (c : List ℕ)
    (hc : Traj d θ G c) :
    (Bset c t).card = lvl c t ∧ (Aset c t).card = lvl c t ∧
      (∀ b ∈ Bset c t, b < n) ∧ (∀ a ∈ Aset c t, a < n) ∧
      (∀ a ∈ Aset c t, phiN C (partner c t a) < k) ∧
      EvT (t - 1) (Bset c t)
        (tau G (phiN C) (Bset c t) (Aset c t) (fun a => phiN C (partner c t a))
          (rank G (phiN C) c t)) c := by
  refine ⟨card_Bset c t (by omega), card_Aset c t ht2,
    fun b hb => traj_lt_n hc ((mem_Bset c t b).1 hb).1,
    fun a ha => traj_lt_n hc ((mem_Aset c t a).1 ha).1, fun a ha => ?_, ?_⟩
  · have hp := partner_spec c t ht2 a ha
    have hpn := traj_lt_n hc ((mem_Bset c t _).1 hp.1).1
    unfold phiN
    rw [dif_pos hpn]
    exact (C _).isLt
  · intro b hb _
    have hbB := (mem_Bset c t b).1 hb
    have hcnt := Bset_count_take c t b hb
    obtain ⟨v, hvb, hvl, hvx, hvc⟩ :=
      exists_pos_count_take c (c.getD b 0) (t - 2) b (by omega)
    have hvA : v ∈ Aset c t :=
      (mem_Aset c t v).2 ⟨hvl, by rw [hvx]; exact hbB.2.1, by unfold occ; rw [hvx, hvc]; omega⟩
    have hpv : partner c t v = b := partner_eq c t v b hb hvx.symm
    set F := (Aset c t).filter (fun a => a < b ∧
      beta G (phiN C) (c.take b) (Bset c t) ((fun a => phiN C (partner c t a)) a)
        (rank G (phiN C) c t a) a = b) with hF
    have hFv : F = {v} := by
      ext a
      simp only [hF, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hab, hbeta⟩
        rw [beta_take G _ c _ _ _ b a hab, beta_partner hc _ t ht2 a ha] at hbeta
        have hsp := partner_spec c t ht2 a ha
        rw [hbeta] at hsp
        have haA := (mem_Aset c t a).1 ha
        have hvA' := (mem_Aset c t v).1 hvA
        exact pos_eq_of_occ c a v haA.1 hvl (by rw [← hsp.2.1, hvx]) (by omega)
      · intro h
        rw [h]
        refine ⟨hvA, hvb, ?_⟩
        rw [beta_take G _ c _ _ _ b v hvb, beta_partner hc _ t ht2 v hvA, hpv]
    have htau : tau G (phiN C) (Bset c t) (Aset c t) (fun a => phiN C (partner c t a))
        (rank G (phiN C) c t) b (c.take b) = c.getD b 0 := by
      have hne : F.Nonempty := by rw [hFv]; exact Finset.singleton_nonempty v
      unfold tau
      rw [dif_pos hne]
      have hmin : F.min' hne ∈ ({v} : Finset ℕ) := by rw [← hFv]; exact F.min'_mem hne
      rw [Finset.mem_singleton.1 hmin, getD_take_of_lt c b v hvb, hvx]
    rw [htau]
    exact ⟨hcnt, rfl⟩

end OnlineColoringKYY.Supplement.Dev.T515.PartS1
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part S1: the profile of a final coloring (Definitions 5.7–5.9, decoding of Lemma 5.10) -/
alias profile_basic := OnlineColoringKYY.Supplement.Dev.T515.PartS1.profile_basic

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartS2
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515 OnlineColoringKYY.Supplement.Dev.T515.PartS1
lemma count_take_le_count (c : List ℕ) (j x : ℕ) : (c.take j).count x ≤ c.count x :=
  (List.take_sublist j c).count_le x

lemma occ_le_count (c : List ℕ) (u : ℕ) (hu : u < c.length) : occ c u ≤ c.count (c.getD u 0) := by
  have h1 := count_take_succ c u (c.getD u 0)
  rw [if_pos ⟨hu, rfl⟩] at h1
  have h2 := count_take_le_count c (u + 1) (c.getD u 0)
  unfold occ
  omega

/-- Per-`b'` bound: the elements of `A` charged to `b'` are at most `θ t - 1`. -/
lemma per_b_le (d : ℕ) (θ : ℕ → ℕ)
    (hθ : ∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.Coloring (Fin k)) (t : ℕ) (ht2 : 2 ≤ t) (htd : t ≤ d - 1) (c : List ℕ)
    (hc : Traj d θ G c) (b' : ℕ) (hb' : b' ∈ Bset c t) :
    ((Aset c t).filter (fun a =>
      b' ∈ Eset G (phiN C) c (Bset c t) (phiN C (partner c t a)) a ∧ partner c t a < b')).card
      ≤ θ t - 1 := by
  have hbB := (mem_Bset c t b').1 hb'
  have hbl : b' < c.length := hbB.1
  have hbn : b' < n := traj_lt_n hc hbl
  set p := c.take b' with hp
  set v : Fin n := ⟨b', hbn⟩ with hv
  have hcnt : p.count (c.getD b' 0) = t - 1 := Bset_count_take c t b' hb'
  -- level `t` does not qualify at `b'`
  have hnot : ¬ LvOK θ G v p t := by
    rcases step_support d θ G v p _ (traj_step hc b' hbl) with h | ⟨i, hi1, hid, hix, -, hj⟩
    · exfalso
      apply h.2.1
      exact List.count_pos_iff.1 (by rw [hcnt]; omega)
    · have := ((mem_eligibleLevel G v p i _).1 hix).2.1
      rw [hcnt] at this
      exact hj t (by omega) htd
  have hcard : (eligibleLevel G v p t).card ≤ θ t - 1 := by
    have hθt := hθ t (by omega) htd
    by_cases hne : (eligibleLevel G v p t).Nonempty
    · have : ¬ θ t ≤ (eligibleLevel G v p t).card := fun h => hnot ⟨hne, h⟩
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  refine le_trans (Finset.card_le_card_of_injOn (fun a => c.getD a 0) ?_ ?_) hcard
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    obtain ⟨haA, hbE, hpb⟩ := ha
    have haA' := (mem_Aset c t a).1 haA
    obtain ⟨hpB, hpe, hap⟩ := partner_spec c t ht2 a haA
    have hpB' := (mem_Bset c t _).1 hpB
    set x := c.getD a 0 with hx
    show x ∈ eligibleLevel G v p t
    -- count of `x` in the prefix
    have hpc : p.count x = t := by
      have h1 := Bset_count_take c t _ hpB
      have h2 := count_take_succ c (partner c t a) (c.getD (partner c t a) 0)
      rw [if_pos ⟨hpB'.1, rfl⟩] at h2
      have h3 := count_take_mono c (c.getD (partner c t a) 0) (show partner c t a + 1 ≤ b' by omega)
      have h4 := count_take_le_count c b' (c.getD (partner c t a) 0)
      rw [hpe] at h1 h2 h3 h4
      rw [hp]
      have : c.count x = t := haA'.2.1
      omega
    rw [mem_eligibleLevel]
    refine ⟨List.count_pos_iff.1 (by rw [hpc]; omega), hpc, ?_⟩
    intro u hub hadj hux
    have hub : u < b' := hub
    have hadj' : adjN G u b' := adjN_of_prefixAdj G u b' hbn hadj
    rw [hp, getD_take_of_lt c b' u hub] at hux
    have hEs := (Finset.mem_filter.1 hbE).2
    by_cases hua : u ≤ a
    · exact hEs.2 u (by simp only [grp, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hux⟩)
        hadj'
    · have hul : u < c.length := by omega
      have h1 := occ_lt c a u (by omega) haA'.1 hux.symm
      have h2 := occ_le_count c u hul
      rw [hux] at h2
      have hup : u = partner c t a :=
        pos_eq_of_occ c u _ hul hpB'.1 (by rw [hux, hpe]) (by omega)
      subst hup
      obtain ⟨hun, hbn', hG⟩ := hadj'
      have hφ := hEs.1
      unfold phiN at hφ
      rw [dif_pos hun, dif_pos hbn'] at hφ
      exact C.valid hG (Fin.ext hφ.symm)
  · intro a1 h1 a2 h2 he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at h1 h2
    have h1' := (mem_Aset c t a1).1 h1.1
    have h2' := (mem_Aset c t a2).1 h2.1
    exact pos_eq_of_occ c a1 a2 h1'.1 h2'.1 he (by omega)

theorem rank_sum_le (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ)
    (hθ : ∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.Coloring (Fin k)) (t : ℕ) (ht2 : 2 ≤ t) (htd : t ≤ d - 1) (c : List ℕ)
    (hc : Traj d θ G c) :
    ∑ a ∈ Aset c t, rank G (phiN C) c t a ≤ (θ t - 1) * lvl c t := by
  set Q : ℕ → ℕ → Prop := fun a b =>
    b ∈ Eset G (phiN C) c (Bset c t) (phiN C (partner c t a)) a ∧ partner c t a < b with hQ
  have hr : ∀ a, rank G (phiN C) c t a = ((Bset c t).filter (fun b => Q a b)).card := by
    intro a
    unfold rank
    congr 1
    ext b
    simp only [hQ, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(Finset.mem_filter.1 h1).1, h1, h2⟩
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  calc ∑ a ∈ Aset c t, rank G (phiN C) c t a
      = ∑ a ∈ Aset c t, ∑ b ∈ Bset c t, if Q a b then 1 else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hr, Finset.card_filter]
    _ = ∑ b ∈ Bset c t, ∑ a ∈ Aset c t, if Q a b then 1 else 0 := Finset.sum_comm
    _ = ∑ b ∈ Bset c t, ((Aset c t).filter (fun a => Q a b)).card := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.card_filter]
    _ ≤ ∑ b ∈ Bset c t, (θ t - 1) :=
        Finset.sum_le_sum fun b hb => per_b_le d θ hθ G C t ht2 htd c hc b hb
    _ = (θ t - 1) * lvl c t := by
        rw [Finset.sum_const, card_Bset c t (by omega), smul_eq_mul, mul_comm]

end OnlineColoringKYY.Supplement.Dev.T515.PartS2
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part S2: paper's Lemma 5.11 -/
alias rank_sum_le := OnlineColoringKYY.Supplement.Dev.T515.PartS2.rank_sum_le

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartP
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
/-! ### Basic helpers -/
theorem outer_le_one {α : Type*} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 := by
  calc p.toOuterMeasure s ≤ p.toOuterMeasure Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).2 (Set.subset_univ _)

theorem lt_freshColor (c : List ℕ) : ∀ x ∈ c, x < freshColor c := by
  induction c with
  | nil => simp
  | cons y l ih =>
    intro x hx
    simp only [freshColor, List.foldr_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih x hx) (le_max_right _ _)

theorem run_length (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ (m : ℕ) (h : m ≤ n) (c : List ℕ), dLevelRun d θ G m h c ≠ 0 → c.length = m := by
  intro m
  induction m with
  | zero =>
    intro h c hc
    simp only [dLevelRun, PMF.pure_apply, ne_eq, ite_eq_right_iff, not_forall] at hc
    obtain ⟨rfl, _⟩ := hc
    rfl
  | succ m ih =>
    intro h c hc
    have hc' : c ∈ (dLevelRun d θ G (m+1) h).support := hc
    simp only [dLevelRun, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hc'
    obtain ⟨e, he, x, _, rfl⟩ := hc'
    simp [ih _ e he]

/-- One step: a color of current count `s ≥ 1` is chosen with probability at most `1 / θ s`. -/
theorem step_le (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (c : List ℕ) (y s : ℕ) (hs : 1 ≤ s) (hy : c.count y = s) :
    dLevelStep d θ G v c y ≤ ((θ s : ENNReal))⁻¹ := by
  have hyc : y ∈ c := List.count_pos_iff.1 (by omega)
  unfold dLevelStep
  dsimp only
  split_ifs with h
  · rw [PMF.uniformOfFinset_apply]
    split_ifs with hm
    · have h2 := (Finset.mem_filter.1 hm).2.1
      have h3 := (Finset.mem_filter.1 (Finset.max'_mem _ h)).2.2
      rw [← hy, h2]
      exact ENNReal.inv_le_inv.2 (by exact_mod_cast h3)
    · exact bot_le
  · have hne : y ≠ freshColor c := fun he => by
      have := lt_freshColor c y hyc
      omega
    simp [PMF.pure_apply, hne]

theorem EvT_of_append (s : ℕ) (B : Finset ℕ) (τ : ℕ → List ℕ → ℕ) (c : List ℕ) (x : ℕ)
    (h : EvT s B τ (c ++ [x])) : EvT s B τ c := by
  intro b hb hlt
  have hl : b < (c ++ [x]).length := by simp; omega
  obtain ⟨h3, h4⟩ := h b hb hl
  have e1 : (c ++ [x]).take b = c.take b := List.take_append_of_le_length hlt.le
  have e3 : (c ++ [x]).getD b 0 = c.getD b 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  rw [e1] at h3 h4
  rw [e3] at h4
  exact ⟨h3, h4⟩

theorem EvT_append_last (s : ℕ) (B : Finset ℕ) (τ : ℕ → List ℕ → ℕ) (c : List ℕ) (x : ℕ)
    (hb : c.length ∈ B) (h : EvT s B τ (c ++ [x])) :
    c.count (τ c.length c) = s ∧ x = τ c.length c := by
  obtain ⟨h3, h4⟩ := h _ hb (by simp)
  have e1 : (c ++ [x]).take c.length = c := by simp
  have e3 : (c ++ [x]).getD c.length 0 = x := by simp [List.getD_eq_getElem?_getD]
  rw [e1] at h3 h4
  rw [e3] at h4
  exact ⟨h3, h4⟩

theorem prob_EvT_le (d : ℕ) (θ : ℕ → ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) (hs : 1 ≤ s)
    (B : Finset ℕ) (τ : ℕ → List ℕ → ℕ) (m : ℕ) (h : m ≤ n) :
    (dLevelRun d θ G m h).toOuterMeasure {c | EvT s B τ c} ≤
      ((θ s : ENNReal)⁻¹) ^ (B.filter (fun b => b < m)).card := by
  induction m with
  | zero =>
    have : B.filter (fun b => b < 0) = ∅ := by
      ext q; simp
    rw [this, Finset.card_empty, pow_zero]
    exact outer_le_one _ _
  | succ m ih =>
    have ih' := ih (Nat.le_of_succ_le h)
    set μ := dLevelRun d θ G m (Nat.le_of_succ_le h) with hμdef
    set r : ENNReal := if m ∈ B then (θ s : ENNReal)⁻¹ else 1 with hr
    have hcard : ((θ s : ENNReal)⁻¹) ^ (B.filter (fun b => b < m)).card * r ≤
        ((θ s : ENNReal)⁻¹) ^ (B.filter (fun b => b < m + 1)).card := by
      by_cases hex : m ∈ B
      · have hr' : r = (θ s : ENNReal)⁻¹ := if_pos hex
        have heq : B.filter (fun b => b < m + 1) = insert m (B.filter (fun b => b < m)) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hq, hqm⟩
            by_cases hq2 : q = m
            · left; exact hq2
            · right; exact ⟨hq, by omega⟩
          · rintro (rfl | ⟨hq, hqm⟩)
            · exact ⟨hex, by omega⟩
            · exact ⟨hq, by omega⟩
        have hnot : m ∉ B.filter (fun b => b < m) := by simp
        rw [heq, Finset.card_insert_of_notMem hnot, pow_succ, hr']
      · have hr' : r = 1 := if_neg hex
        have heq : B.filter (fun b => b < m + 1) = B.filter (fun b => b < m) := by
          ext q
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hq, hqm⟩
            refine ⟨hq, ?_⟩
            by_contra hc
            exact hex (by rwa [show q = m by omega] at hq)
          · rintro ⟨hq, hqm⟩; exact ⟨hq, by omega⟩
        rw [heq, hr', mul_one]
    have key : ∀ c, μ c * (dLevelStep d θ G ⟨m, h⟩ c).toOuterMeasure
        ((fun x => c ++ [x]) ⁻¹' {c | EvT s B τ c}) ≤
          ({c | EvT s B τ c}.indicator μ c) * r := by
      intro c
      by_cases hμ : μ c = 0
      · simp [hμ]
      have hlen := run_length d θ G m (Nat.le_of_succ_le h) c hμ
      by_cases hE : EvT s B τ c
      · rw [Set.indicator_of_mem (show c ∈ {c | EvT s B τ c} from hE)]
        gcongr
        by_cases hex : m ∈ B
        · have hr' : r = (θ s : ENNReal)⁻¹ := if_pos hex
          rw [hr']
          have hexl : c.length ∈ B := by rw [hlen]; exact hex
          by_cases hc1 : c.count (τ c.length c) = s
          · have hsub : ((fun x => c ++ [x]) ⁻¹' {c | EvT s B τ c}) ⊆ {τ c.length c} := by
              intro x hx
              exact (EvT_append_last s B τ c x hexl hx).2
            calc _ ≤ (dLevelStep d θ G ⟨m, h⟩ c).toOuterMeasure {τ c.length c} :=
                  MeasureTheory.measure_mono hsub
              _ = dLevelStep d θ G ⟨m, h⟩ c (τ c.length c) :=
                  PMF.toOuterMeasure_apply_singleton _ _
              _ ≤ _ := step_le d θ G _ c _ s hs hc1
          · have hemp : ((fun x => c ++ [x]) ⁻¹' {c | EvT s B τ c}) = ∅ := by
              ext x
              simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              intro hx
              exact hc1 (EvT_append_last s B τ c x hexl hx).1
            rw [hemp, MeasureTheory.measure_empty]
            exact bot_le
        · have hr' : r = 1 := if_neg hex
          rw [hr']
          exact outer_le_one _ _
      · have hemp : ((fun x => c ++ [x]) ⁻¹' {c | EvT s B τ c}) = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hx
          exact hE (EvT_of_append s B τ c x hx)
        rw [hemp, MeasureTheory.measure_empty, mul_zero]
        exact bot_le
    calc (dLevelRun d θ G (m + 1) h).toOuterMeasure {c | EvT s B τ c}
        = ∑' c, μ c * ((dLevelStep d θ G ⟨m, h⟩ c).map (fun x => c ++ [x])).toOuterMeasure
            {c | EvT s B τ c} := by
          rw [dLevelRun, PMF.toOuterMeasure_bind_apply]
      _ = ∑' c, μ c * (dLevelStep d θ G ⟨m, h⟩ c).toOuterMeasure
            ((fun x => c ++ [x]) ⁻¹' {c | EvT s B τ c}) := by
          simp_rw [PMF.toOuterMeasure_map_apply]
      _ ≤ ∑' c, ({c | EvT s B τ c}.indicator μ c) * r := ENNReal.tsum_le_tsum key
      _ = (∑' c, {c | EvT s B τ c}.indicator μ c) * r := ENNReal.tsum_mul_right
      _ = μ.toOuterMeasure {c | EvT s B τ c} * r := by rw [PMF.toOuterMeasure_apply]
      _ ≤ ((θ s : ENNReal)⁻¹) ^ (B.filter (fun b => b < m)).card * r := by gcongr
      _ ≤ _ := hcard

end OnlineColoringKYY.Supplement.Dev.T515.PartP
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part P: probability (Lemma 5.10) and the union bound (Lemmas 5.12, 5.13) -/

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartP
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
/-! ### The union bound -/
/-- Extend a function on `A` by zero. -/
def extF (A : Finset ℕ) (f : (a : ℕ) → a ∈ A → ℕ) : ℕ → ℕ :=
  fun a => if h : a ∈ A then f a h else 0

/-- Color choices on `A`. -/
noncomputable def PK (k : ℕ) (A : Finset ℕ) : Finset ((a : ℕ) → a ∈ A → ℕ) :=
  A.pi (fun _ => Finset.range k)

/-- Rank choices on `A` with sum at most `S`. -/
noncomputable def PR (S : ℕ) (A : Finset ℕ) : Finset ((a : ℕ) → a ∈ A → ℕ) :=
  (A.pi (fun _ => Finset.range (S + 1))).filter (fun f => ∑ a ∈ A.attach, f a.1 a.2 ≤ S)

theorem tau_congr {n : ℕ} (G : SimpleGraph (Fin n)) (φ : ℕ → ℕ) (B A : Finset ℕ)
    (col r col' r' : ℕ → ℕ) (hc : ∀ a ∈ A, col a = col' a) (hr : ∀ a ∈ A, r a = r' a) :
    tau G φ B A col r = tau G φ B A col' r' := by
  funext b p
  have hf : A.filter (fun a => a < b ∧ beta G φ p B (col a) (r a) a = b) =
      A.filter (fun a => a < b ∧ beta G φ p B (col' a) (r' a) a = b) :=
    Finset.filter_congr (fun a ha => by rw [hc a ha, hr a ha])
  unfold tau
  simp only [hf]

theorem card_PK (k : ℕ) (A : Finset ℕ) : (PK k A).card = k ^ A.card := by
  unfold PK
  rw [Finset.card_pi, Finset.prod_const, Finset.card_range]

/-- Stars and bars. -/
theorem card_PR_le (S : ℕ) (A : Finset ℕ) : (PR S A).card ≤ (S + A.card).choose A.card := by
  let M : ((a : ℕ) → a ∈ A → ℕ) → Multiset (Option A) := fun f =>
    ∑ a ∈ A.attach, f a.1 a.2 • ({some a} : Multiset (Option A)) +
      (S - ∑ a ∈ A.attach, f a.1 a.2) • ({none} : Multiset (Option A))
  let T : Finset (Multiset (Option A)) :=
    Finset.image (fun s : Sym (Option A) S => (s : Multiset (Option A))) Finset.univ
  have hmaps : Set.MapsTo M (PR S A : Set _) (T : Set _) := by
    intro f hf
    have hf' := (Finset.mem_filter.1 hf).2
    have hcard : Multiset.card (M f) = S := by
      simp only [M, Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
        Multiset.card_sum]
      omega
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨Sym.mk (M f) hcard, Finset.mem_univ _, rfl⟩
  have hinj : Set.InjOn M (PR S A : Set _) := by
    intro f _ g _ hfg
    funext a ha
    have := congrArg (Multiset.count (some ⟨a, ha⟩)) hfg
    simp only [M, Multiset.count_add, Multiset.count_sum', Multiset.count_nsmul,
      Multiset.count_singleton] at this
    simpa using this
  calc (PR S A).card ≤ T.card := Finset.card_le_card_of_injOn M hmaps hinj
    _ ≤ (Finset.univ : Finset (Sym (Option A) S)).card := by
        simp only [T]; exact Finset.card_image_le
    _ = (Fintype.card (Option A) + S - 1).choose S := by
        rw [Finset.card_univ, Sym.card_sym_eq_choose]
    _ = (S + A.card).choose A.card := by
        rw [Fintype.card_option, Fintype.card_coe,
          show A.card + 1 + S - 1 = S + A.card by omega, Nat.choose_symm_add]

theorem prob_lvl_eq (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ)
    (hθ : ∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Colorable k) (t : ℕ) (ht2 : 2 ≤ t) (htd : t ≤ d - 1) (m : ℕ) :
    (dLevelRun d θ G n le_rfl).toOuterMeasure {c | lvl c t = m} ≤
      (n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((θ t * m).choose m : ENNReal) *
        ((θ (t - 1) : ENNReal)⁻¹) ^ m := by
  obtain ⟨C⟩ := hG
  set μ := dLevelRun d θ G n le_rfl with hμdef
  set S := (θ t - 1) * m with hSdef
  set PS := (Finset.range n).powersetCard m with hPS
  set x : ENNReal := ((θ (t - 1) : ENNReal)⁻¹) ^ m with hx
  have hθt : 1 ≤ θ t := hθ t (by omega) htd
  have hSm : S + m = θ t * m := by
    obtain ⟨j, hj⟩ : ∃ j, θ t = j + 1 := ⟨θ t - 1, by omega⟩
    rw [hSdef, hj, Nat.add_sub_cancel]; ring
  have hcover : ∀ c, {c | lvl c t = m}.indicator μ c ≤
      ∑ B ∈ PS, ∑ A ∈ PS, ∑ cf ∈ PK k A, ∑ rf ∈ PR S A,
        {c | EvT (t - 1) B (tau G (phiN C) B A (extF A cf) (extF A rf)) c}.indicator μ c := by
    intro c
    by_cases hlv : lvl c t = m
    swap
    · rw [Set.indicator_of_notMem (show c ∉ {c | lvl c t = m} from hlv)]
      exact bot_le
    rw [Set.indicator_of_mem (show c ∈ {c | lvl c t = m} from hlv)]
    by_cases hμ : μ c = 0
    · rw [hμ]; exact bot_le
    obtain ⟨_, htraj⟩ := run_support d θ G n le_rfl c ((PMF.mem_support_iff _ _).2 hμ)
    obtain ⟨hBc, hAc, hBn, hAn, hcol, hEv⟩ := profile_basic d hd θ hθ G C t ht2 htd c htraj
    have hrank := rank_sum_le d hd θ hθ G C t ht2 htd c htraj
    rw [hlv] at hBc hAc hrank
    let cf : (a : ℕ) → a ∈ Aset c t → ℕ := fun a _ => phiN C (partner c t a)
    let rf : (a : ℕ) → a ∈ Aset c t → ℕ := fun a _ => rank G (phiN C) c t a
    have hBS : Bset c t ∈ PS := by
      rw [hPS, Finset.mem_powersetCard]
      exact ⟨fun b hb => Finset.mem_range.2 (hBn b hb), hBc⟩
    have hAS : Aset c t ∈ PS := by
      rw [hPS, Finset.mem_powersetCard]
      exact ⟨fun a ha => Finset.mem_range.2 (hAn a ha), hAc⟩
    have hcf : cf ∈ PK k (Aset c t) :=
      Finset.mem_pi.2 (fun a ha => Finset.mem_range.2 (hcol a ha))
    have hsum : ∑ a ∈ (Aset c t).attach, rf a.1 a.2 = ∑ a ∈ Aset c t, rank G (phiN C) c t a :=
      Finset.sum_attach (Aset c t) (fun a => rank G (phiN C) c t a)
    have hrf : rf ∈ PR S (Aset c t) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_pi.2 (fun a ha => Finset.mem_range.2 ?_), ?_⟩
      · exact Nat.lt_succ_of_le (le_trans (Finset.single_le_sum
          (f := fun a => rank G (phiN C) c t a) (fun _ _ => Nat.zero_le _) ha) hrank)
      · rw [hsum]; exact hrank
    have htau : tau G (phiN C) (Bset c t) (Aset c t) (extF (Aset c t) cf) (extF (Aset c t) rf) =
        tau G (phiN C) (Bset c t) (Aset c t) (fun a => phiN C (partner c t a))
          (rank G (phiN C) c t) :=
      tau_congr _ _ _ _ _ _ _ _ (fun a ha => by simp [extF, ha, cf])
        (fun a ha => by simp [extF, ha, rf])
    have hterm : {e | EvT (t - 1) (Bset c t) (tau G (phiN C) (Bset c t) (Aset c t)
        (extF (Aset c t) cf) (extF (Aset c t) rf)) e}.indicator μ c = μ c := by
      rw [htau]
      exact Set.indicator_of_mem (show c ∈ {e | EvT (t - 1) (Bset c t) _ e} from hEv) _
    refine le_trans (le_of_eq hterm.symm) ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun B => ∑ A ∈ PS, ∑ cf ∈ PK k A,
      ∑ rf ∈ PR S A, {e | EvT (t - 1) B (tau G (phiN C) B A (extF A cf) (extF A rf)) e}.indicator
        μ c) (fun _ _ => zero_le) hBS)
    refine le_trans ?_ (Finset.single_le_sum (f := fun A => ∑ cf ∈ PK k A,
      ∑ rf ∈ PR S A, {e | EvT (t - 1) (Bset c t) (tau G (phiN C) (Bset c t) A (extF A cf)
        (extF A rf)) e}.indicator μ c) (fun _ _ => zero_le) hAS)
    refine le_trans ?_ (Finset.single_le_sum (f := fun cf => ∑ rf ∈ PR S (Aset c t),
      {e | EvT (t - 1) (Bset c t) (tau G (phiN C) (Bset c t) (Aset c t) (extF (Aset c t) cf)
        (extF (Aset c t) rf)) e}.indicator μ c) (fun _ _ => zero_le) hcf)
    exact Finset.single_le_sum (f := fun g => {e | EvT (t - 1) (Bset c t)
      (tau G (phiN C) (Bset c t) (Aset c t) (extF (Aset c t) cf) (extF (Aset c t) g)) e}.indicator
        μ c) (fun _ _ => zero_le) hrf
  have hterm : ∀ B ∈ PS, ∀ A : Finset ℕ, ∀ cf rf,
      ∑' c, {c | EvT (t - 1) B (tau G (phiN C) B A (extF A cf) (extF A rf)) c}.indicator μ c
        ≤ x := by
    intro B hB A cf rf
    rw [← PMF.toOuterMeasure_apply]
    have hfilt : B.filter (fun b => b < n) = B := by
      apply Finset.filter_true_of_mem
      intro b hb
      exact Finset.mem_range.1 ((Finset.mem_powersetCard.1 hB).1 hb)
    have := prob_EvT_le d θ G (t - 1) (by omega) B
      (tau G (phiN C) B A (extF A cf) (extF A rf)) n le_rfl
    rw [hfilt, (Finset.mem_powersetCard.1 hB).2] at this
    exact this
  have hPR : ∀ A ∈ PS, ((PR S A).card : ENNReal) ≤ ((θ t * m).choose m : ℕ) := by
    intro A hA
    have := card_PR_le S A
    rw [(Finset.mem_powersetCard.1 hA).2, hSm] at this
    exact_mod_cast this
  have hPK : ∀ A ∈ PS, ((PK k A).card : ENNReal) = (k : ENNReal) ^ m := by
    intro A hA
    rw [card_PK, (Finset.mem_powersetCard.1 hA).2]
    push_cast; rfl
  calc μ.toOuterMeasure {c | lvl c t = m} = ∑' c, {c | lvl c t = m}.indicator μ c :=
        PMF.toOuterMeasure_apply _ _
    _ ≤ ∑' c, ∑ B ∈ PS, ∑ A ∈ PS, ∑ cf ∈ PK k A, ∑ rf ∈ PR S A,
        {c | EvT (t - 1) B (tau G (phiN C) B A (extF A cf) (extF A rf)) c}.indicator μ c :=
        ENNReal.tsum_le_tsum hcover
    _ = ∑ B ∈ PS, ∑ A ∈ PS, ∑ cf ∈ PK k A, ∑ rf ∈ PR S A, ∑' c,
        {c | EvT (t - 1) B (tau G (phiN C) B A (extF A cf) (extF A rf)) c}.indicator μ c := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun B _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun cf _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ B ∈ PS, ∑ A ∈ PS, ∑ cf ∈ PK k A, ∑ rf ∈ PR S A, x := by
        gcongr with B hB A hA cf hcf rf hrf
        exact hterm B hB A cf rf
    _ = ∑ B ∈ PS, ∑ A ∈ PS, ((PK k A).card : ENNReal) * (((PR S A).card : ENNReal) * x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ B ∈ PS, ∑ A ∈ PS, (k : ENNReal) ^ m * ((((θ t * m).choose m : ℕ) : ENNReal) * x) := by
        gcongr with B hB A hA
        · exact (hPK A hA).le
        · exact_mod_cast hPR A hA
    _ = (n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((θ t * m).choose m : ENNReal) * x := by
        simp only [Finset.sum_const, nsmul_eq_mul, hPS, Finset.card_powersetCard,
          Finset.card_range]
        ring

end OnlineColoringKYY.Supplement.Dev.T515.PartP
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias prob_lvl_eq := OnlineColoringKYY.Supplement.Dev.T515.PartP.prob_lvl_eq

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartE
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
theorem tsum_geom_two : ∑' j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) = 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hR : ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr]; norm_num
  have hS : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hterm : ∀ j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) =
      ENNReal.ofReal ((j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    intro j
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_natCast, mul_comm, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hS, hR]
  simp

theorem lvl_zero (c : List ℕ) : lvl c 0 = 0 := by
  unfold lvl
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [List.mem_toFinset] at hx
  exact (List.count_pos_iff.2 hx).ne'

/-- `E[lvl_t] ≤ m₀ + 2` from a tail bound on `Pr[lvl_t = m]`. -/
theorem exp_lvl_le (μ : PMF (List ℕ)) (t m₀ : ℕ)
    (hPr_le : ∀ j, m₀ ≤ j → μ.toOuterMeasure {c | lvl c t = j} ≤ (2⁻¹) ^ j) :
    ∑' c, μ c * (lvl c t : ENNReal) ≤ m₀ + 2 := by
  set Pr : ℕ → ENNReal := fun j => ∑' c, {c | lvl c t = j}.indicator μ c with hPr
  have hPr_le' : ∀ j, m₀ ≤ j → Pr j ≤ (2⁻¹) ^ j := by
    intro j hj
    have := hPr_le j hj
    rw [PMF.toOuterMeasure_apply] at this
    exact this
  have hPr_sum : ∑' j, Pr j = 1 := by
    simp only [hPr]
    rw [ENNReal.tsum_comm]
    rw [← PMF.tsum_coe μ]
    refine tsum_congr (fun c => ?_)
    rw [tsum_eq_single (lvl c t)]
    · exact Set.indicator_of_mem (show c ∈ {d | lvl d t = lvl c t} from rfl) _
    · intro j hj
      exact Set.indicator_of_notMem (show c ∉ {d | lvl d t = j} from fun h => hj h.symm) _
  have e1 : ∀ c, μ c * (lvl c t : ENNReal) =
      ∑' j, {c | lvl c t = j}.indicator μ c * (j : ENNReal) := by
    intro c
    rw [tsum_eq_single (lvl c t)]
    · rw [Set.indicator_of_mem (show c ∈ {d | lvl d t = lvl c t} from rfl)]
    · intro j hj
      rw [Set.indicator_of_notMem (show c ∉ {d | lvl d t = j} from fun h => hj h.symm), zero_mul]
  calc ∑' c, μ c * (lvl c t : ENNReal)
      = ∑' c, ∑' j, {c | lvl c t = j}.indicator μ c * (j : ENNReal) := tsum_congr e1
    _ = ∑' j, ∑' c, {c | lvl c t = j}.indicator μ c * (j : ENNReal) := ENNReal.tsum_comm
    _ = ∑' j, Pr j * (j : ENNReal) := by
        refine tsum_congr (fun j => ?_)
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' j, (Pr j * (m₀ : ENNReal) + ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal)) := by
        refine ENNReal.tsum_le_tsum (fun j => ?_)
        by_cases hj : j < m₀
        · calc Pr j * (j : ENNReal) ≤ Pr j * (m₀ : ENNReal) := by
                gcongr
            _ ≤ _ := le_self_add
        · calc Pr j * (j : ENNReal) ≤ ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) := by
                gcongr
                exact hPr_le' j (by omega)
            _ ≤ _ := le_add_self
    _ = (∑' j, Pr j) * (m₀ : ENNReal) + ∑' j : ℕ, ((2 : ENNReal)⁻¹) ^ j * (j : ENNReal) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = m₀ + 2 := by rw [hPr_sum, one_mul, tsum_geom_two]

theorem sum_range_split (d : ℕ) (hd : 2 ≤ d) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range d, f t = f 0 + f 1 + ∑ t ∈ Finset.Icc 2 (d - 1), f t := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have : Finset.Icc 2 (e + 2 - 1) = Finset.Ico 2 (e + 2) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [add_comm (f 0), add_assoc, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1; omega

theorem expColors_le (d : ℕ) (hd : 2 ≤ d) (θ : ℕ → ℕ)
    (hθ : ∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Colorable k) (m₀ : ℕ → ℕ)
    (htail : ∀ t, 2 ≤ t → t ≤ d - 1 → ∀ m, m₀ t ≤ m →
      (n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((θ t * m).choose m : ENNReal) *
        ((θ (t - 1) : ENNReal)⁻¹) ^ m ≤ (2⁻¹) ^ m) :
    (d : ENNReal) * expColors (dLevelRun d θ G n le_rfl) ≤
      ((n + (d - 1) * (k * θ 1) +
        ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * (m₀ t + 2) : ℕ) : ENNReal) := by
  set μ := dLevelRun d θ G n le_rfl with hμdef
  set A : ℕ := n + (d - 1) * (k * θ 1) with hA
  have hθ1 : 1 ≤ θ 1 := hθ 1 le_rfl (by omega)
  have hL : ∀ t ∈ Finset.Icc 2 (d - 1), ∑' c, μ c * (lvl c t : ENNReal) ≤ (m₀ t + 2 : ℕ) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    push_cast
    refine exp_lvl_le μ t (m₀ t) (fun j hj => ?_)
    exact (prob_lvl_eq d hd θ hθ G hG t ht.1 ht.2 j).trans (htail t ht.1 ht.2 j hj)
  have hpt : ∀ c, μ c * ((d * c.toFinset.card : ℕ) : ENNReal) ≤
      μ c * (A : ENNReal) +
        ∑ t ∈ Finset.Icc 2 (d - 1), ((d - t : ℕ) : ENNReal) * (μ c * (lvl c t : ENNReal)) := by
    intro c
    by_cases hμ : μ c = 0
    · simp [hμ]
    obtain ⟨hlen, htraj⟩ := run_support d θ G n le_rfl c ((PMF.mem_support_iff _ _).2 hμ)
    have h3 := card_toFinset_eq d c (count_le_d d hd θ G c htraj)
    have h1 := lvl_one_le d hd θ hθ1 G hG c htraj
    have hle : d * c.toFinset.card ≤
        A + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * lvl c t := by
      rw [h3, hlen, sum_range_split d hd (fun t => (d - t) * lvl c t), lvl_zero, hA]
      have : (d - 1) * lvl c 1 ≤ (d - 1) * (k * θ 1) := Nat.mul_le_mul_left _ h1
      simp only [mul_zero, zero_add]
      omega
    have hcast : ((A + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * lvl c t : ℕ) : ENNReal) =
        (A : ENNReal) + ∑ t ∈ Finset.Icc 2 (d - 1), ((d - t : ℕ) : ENNReal) * (lvl c t : ENNReal) := by
      rw [Nat.cast_add, Nat.cast_sum]
      simp_rw [Nat.cast_mul]
    calc μ c * ((d * c.toFinset.card : ℕ) : ENNReal)
        ≤ μ c * ((A + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * lvl c t : ℕ) : ENNReal) := by
          gcongr
      _ = _ := by
          rw [hcast, mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          ring
  have hfin : ((A + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * (m₀ t + 2) : ℕ) : ENNReal) =
      (A : ENNReal) + ∑ t ∈ Finset.Icc 2 (d - 1), ((d - t : ℕ) : ENNReal) * ((m₀ t + 2 : ℕ) : ENNReal) := by
    rw [Nat.cast_add, Nat.cast_sum]
    simp_rw [Nat.cast_mul]
  rw [hfin]
  unfold expColors
  calc (d : ENNReal) * ∑' c, μ c * (c.toFinset.card : ENNReal)
      = ∑' c, μ c * ((d * c.toFinset.card : ℕ) : ENNReal) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun c => ?_)
        push_cast; ring
    _ ≤ ∑' c, (μ c * (A : ENNReal) +
        ∑ t ∈ Finset.Icc 2 (d - 1), ((d - t : ℕ) : ENNReal) * (μ c * (lvl c t : ENNReal))) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' c, μ c) * (A : ENNReal) +
        ∑ t ∈ Finset.Icc 2 (d - 1), ((d - t : ℕ) : ENNReal) * ∑' c, μ c * (lvl c t : ENNReal) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, Summable.tsum_finsetSum
          (fun _ _ => ENNReal.summable)]
        congr 1
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by
        rw [PMF.tsum_coe, one_mul]
        gcongr with t ht
        exact hL t ht

end OnlineColoringKYY.Supplement.Dev.T515.PartE
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part E: expectation -/
alias expColors_le := OnlineColoringKYY.Supplement.Dev.T515.PartE.expColors_le

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartR
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
lemma root_pow (x : ℝ) (hx : 0 ≤ x) (E : ℕ) (hE : 0 < E) : (x ^ (1 / (E : ℝ))) ^ E = x := by
  have : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel this, Real.rpow_one]

lemma rpow_frac (x : ℝ) (hx : 0 ≤ x) (j E : ℕ) :
    x ^ ((j : ℝ) / (E : ℝ)) = (x ^ (1 / (E : ℝ))) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring

/-- Rewriting the two exponents of the statement with `d = e + 2`. -/
lemma exps (e : ℕ) (n k : ℝ) (hn : 0 ≤ n) (hk : 0 ≤ k) :
    n ^ ((2 * ((e + 2 : ℕ) : ℝ) - 4) / (2 * ((e + 2 : ℕ) : ℝ) - 3)) *
      k ^ ((((e + 2 : ℕ) : ℝ) - 1) / (2 * ((e + 2 : ℕ) : ℝ) - 3)) =
    (n ^ (1 / ((2 * e + 1 : ℕ) : ℝ))) ^ (2 * e) * (k ^ (1 / ((2 * e + 1 : ℕ) : ℝ))) ^ (e + 1) := by
  rw [← rpow_frac n hn, ← rpow_frac k hk]
  congr 2
  · congr 1 <;> push_cast <;> ring
  · congr 1 <;> push_cast <;> ring

lemma choose_le (N m : ℕ) (hm : 0 < m) :
    ((N.choose m : ℕ) : ℝ) ≤ ((N : ℝ) * Real.exp 1 / m) ^ m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  refine (Nat.choose_le_pow_div m N).trans ?_
  have h2 := Real.pow_div_factorial_le_exp (m : ℝ) hmpos.le m
  rw [← Real.exp_one_pow, div_le_iff₀ (by positivity)] at h2
  rw [div_pow, mul_pow, le_div_iff₀ (by positivity)]
  calc (N : ℝ) ^ m / (m.factorial : ℝ) * (m : ℝ) ^ m
      = (N : ℝ) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ m * (Real.exp 1 ^ m) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by positivity)]; exact h2

lemma sum_bound (d M : ℕ) :
    (∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * (M + 2)) * 2 ≤ (d + 1) * d * (M + 2) := by
  rw [← Finset.sum_mul]
  have h1 : ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) ≤ ∑ t ∈ Finset.range (d + 1), (d - t) :=
    Finset.sum_le_sum_of_subset (by
      intro x hx; simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]; omega)
  have h2 : ∑ t ∈ Finset.range (d + 1), (d - t) = ∑ t ∈ Finset.range (d + 1), t := by
    have := Finset.sum_range_reflect (fun t => t) (d + 1)
    simpa using this
  have h3 := Finset.sum_range_id_mul_two (d + 1)
  rw [h2] at h1
  simp only [Nat.add_sub_cancel] at h3
  calc (∑ t ∈ Finset.Icc 2 (d - 1), (d - t)) * (M + 2) * 2
      = (∑ t ∈ Finset.Icc 2 (d - 1), (d - t)) * 2 * (M + 2) := by ring
    _ ≤ (∑ t ∈ Finset.range (d + 1), t) * 2 * (M + 2) := by gcongr
    _ = (d + 1) * d * (M + 2) := by rw [h3]

theorem params (d : ℕ) (hd : 2 ≤ d) (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    ∃ (θ : ℕ → ℕ) (m₀ : ℕ → ℕ), (∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) ∧
      (∀ t, 2 ≤ t → t ≤ d - 1 → ∀ m, m₀ t ≤ m →
        (n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((θ t * m).choose m : ENNReal) *
          ((θ (t - 1) : ENNReal)⁻¹) ^ m ≤ (2⁻¹) ^ m) ∧
      ((n + (d - 1) * (k * θ 1) + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * (m₀ t + 2) : ℕ) : ℝ) /
          (d : ℝ) ≤
        (n : ℝ) / (d : ℝ) + 11 * (d : ℝ) *
          (n : ℝ) ^ ((2 * (d : ℝ) - 4) / (2 * (d : ℝ) - 3)) *
          (k : ℝ) ^ (((d : ℝ) - 1) / (2 * (d : ℝ) - 3)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hexp := exps e n k hn0 hk0
  set u := (n : ℝ) ^ (1 / ((2 * e + 1 : ℕ) : ℝ)) with hu
  set v := (k : ℝ) ^ (1 / ((2 * e + 1 : ℕ) : ℝ)) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0 _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hk0 _
  have hun : u ^ (2 * e + 1) = n := root_pow _ hn0 _ (by omega)
  have hvk : v ^ (2 * e + 1) = k := root_pow _ hk0 _ (by omega)
  have hv1 : 1 ≤ v := by
    apply le_of_pow_le_pow_left₀ (n := 2 * e + 1) (by omega) hv0
    rw [hvk, one_pow]; exact_mod_cast hk
  have huv : v < u := by
    apply lt_of_pow_lt_pow_left₀ (2 * e + 1) hu0
    rw [hun, hvk]; exact_mod_cast hkn
  have hu1 : 1 ≤ u := by linarith
  have hvpos : 0 < v := by linarith
  set T := u ^ (2 * e) * v ^ (e + 1) with hT
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu1) (one_le_pow₀ hv1)
  set r := u ^ 2 / v with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hvpos]; nlinarith
  have hrv : (u ^ 2 / v) ^ e * v ^ e = u ^ (2 * e) := by
    rw [← mul_pow, div_mul_cancel₀ _ hvpos.ne', ← pow_mul]
  have hkr : (k : ℝ) * r ^ e = T := by
    rw [← hvk, hr, hT, ← hrv]; ring
  have hrT : r * T ^ 2 = (n : ℝ) ^ 2 * k := by
    rw [← hvk, ← hun, hr, hT, div_mul_eq_mul_div, div_eq_iff hvpos.ne']; ring
  set L := ⌊r⌋₊ with hL
  have hL1 : 1 ≤ L := Nat.le_floor (by exact_mod_cast hr1)
  have hLr : (L : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hLr2 : r ≤ 2 * (L : ℝ) := by
    have h1 : r < L + 1 := Nat.lt_floor_add_one r
    have h2 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  set M := ⌈10 * T⌉₊ with hM
  refine ⟨fun i => L ^ (e + 2 - 1 - i), fun _ => M, ?_, ?_, ?_⟩
  · intro i _ _
    exact Nat.one_le_pow _ _ hL1
  · intro t ht2 htd m hm
    beta_reduce at hm ⊢
    set Θ := L ^ (e + 2 - 1 - t) with hΘ
    have hθt1 : L ^ (e + 2 - 1 - (t - 1)) = L * Θ := by
      rw [show e + 2 - 1 - (t - 1) = (e + 2 - 1 - t) + 1 by omega, pow_succ]; ring
    rw [hθt1]
    have hmT : 10 * T ≤ m := (Nat.ceil_le).1 hm
    have hmpos' : (0 : ℝ) < m := by linarith
    have hmpos : 0 < m := by exact_mod_cast hmpos'
    have hC1 := choose_le n m hmpos
    have hC2 := choose_le (Θ * m) m hmpos
    have hC2' : (((Θ * m).choose m : ℕ) : ℝ) ≤ ((Θ : ℝ) * Real.exp 1) ^ m := by
      refine hC2.trans (le_of_eq ?_)
      congr 1; push_cast; field_simp
    set X := (n : ℝ) * Real.exp 1 / m with hX
    have hX0 : 0 ≤ X := by positivity
    have hE3 : Real.exp 1 ^ 3 ≤ 25 := by
      have := Real.exp_one_lt_d9
      have h0 := Real.exp_pos 1
      calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ h0.le this.le 3
        _ ≤ 25 := by norm_num
    have hbase : X ^ 2 * k * Real.exp 1 * 2 ≤ L := by
      rw [hX, div_pow, mul_pow]
      rw [show (n : ℝ) ^ 2 * Real.exp 1 ^ 2 / (m : ℝ) ^ 2 * k * Real.exp 1 * 2
          = ((n : ℝ) ^ 2 * k * (2 * Real.exp 1 ^ 3)) / (m : ℝ) ^ 2 by ring]
      rw [div_le_iff₀ (by positivity)]
      have hm2 : (10 * T) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmT 2
      have h3 : r * (10 * T) ^ 2 ≤ 2 * (L : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul hLr2 hm2 (by positivity) (by positivity)
      have h4 : (n : ℝ) ^ 2 * k * (2 * Real.exp 1 ^ 3) ≤ (n : ℝ) ^ 2 * k * 50 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : r * (10 * T) ^ 2 = (n : ℝ) ^ 2 * k * 100 := by rw [← hrT]; ring
      nlinarith
    have hΘ0 : (0 : ℝ) ≤ Θ := Nat.cast_nonneg _
    have key : ((n.choose m : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ m * (((Θ * m).choose m : ℕ) : ℝ) * 2 ^ m
        ≤ ((L : ℝ) * Θ) ^ m := by
      calc ((n.choose m : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ m * (((Θ * m).choose m : ℕ) : ℝ) * 2 ^ m
          ≤ (X ^ m) ^ 2 * (k : ℝ) ^ m * (((Θ : ℝ) * Real.exp 1) ^ m) * 2 ^ m := by
            gcongr
        _ = ((X ^ 2 * k * Real.exp 1 * 2) * Θ) ^ m := by ring
        _ ≤ ((L : ℝ) * Θ) ^ m := by
            apply pow_le_pow_left₀ (by positivity)
            exact mul_le_mul_of_nonneg_right hbase hΘ0
    have keyN : (n.choose m) ^ 2 * k ^ m * (Θ * m).choose m * 2 ^ m ≤ (L * Θ) ^ m := by
      exact_mod_cast key
    rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le]
    calc (n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((Θ * m).choose m : ENNReal) *
          (((L * Θ : ℕ) : ENNReal) ^ m)⁻¹ * 2 ^ m
        = ((n.choose m : ENNReal) ^ 2 * (k : ENNReal) ^ m * ((Θ * m).choose m : ENNReal) *
            2 ^ m) / ((L * Θ : ℕ) : ENNReal) ^ m := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast keyN)
  · beta_reduce
    have hAeq : (e + 2 - 1) * (k * L ^ (e + 2 - 1 - 1)) = (e + 1) * (k * L ^ e) := by
      rw [show e + 2 - 1 - 1 = e by omega, show e + 2 - 1 = e + 1 by omega]
    rw [hAeq, mul_assoc (11 * _), hexp]
    have hd : (0 : ℝ) < ((e + 2 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hd]
    have hS := sum_bound (e + 2) M
    set S := ∑ t ∈ Finset.Icc 2 (e + 2 - 1), (e + 2 - t) * (M + 2)
    have hSR : (S : ℝ) * 2 ≤ ((e : ℝ) + 3) * ((e : ℝ) + 2) * ((M : ℝ) + 2) := by
      have : ((S * 2 : ℕ) : ℝ) ≤ (((e + 2 + 1) * (e + 2) * (M + 2) : ℕ) : ℝ) := by
        exact_mod_cast hS
      push_cast at this; linarith
    have hAR : (((e + 1) * (k * L ^ e) : ℕ) : ℝ) ≤ ((e : ℝ) + 1) * T := by
      push_cast
      have h2 : (k : ℝ) * (L : ℝ) ^ e ≤ T := by
        rw [← hkr]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLr e) hk0
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hMT : (M : ℝ) < 10 * T + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [Nat.cast_add, Nat.cast_add]
    have hM2 : (M : ℝ) + 2 ≤ 13 * T := by linarith
    have hS2 : (S : ℝ) * 2 ≤ ((e : ℝ) + 3) * ((e : ℝ) + 2) * (13 * T) :=
      hSR.trans (mul_le_mul_of_nonneg_left hM2 (by positivity))
    have hfin : 0 ≤ T * (9 * (e : ℝ) ^ 2 + 21 * e + 8) := by positivity
    have goalR : ((n : ℝ) / ((e + 2 : ℕ) : ℝ) + 11 * ((e + 2 : ℕ) : ℝ) * T) * ((e + 2 : ℕ) : ℝ)
        = n + 11 * ((e : ℝ) + 2) ^ 2 * T := by
      field_simp; push_cast; ring
    rw [goalR]
    linarith

end OnlineColoringKYY.Supplement.Dev.T515.PartR
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
/-! ### Part R: parameters (real arithmetic) -/
alias params := OnlineColoringKYY.Supplement.Dev.T515.PartR.params

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515.PartR
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T515
theorem trivial_range (d : ℕ) (hd : 2 ≤ d) (n k : ℕ) (hnk : n ≤ k) :
    (n : ℝ) ≤ (n : ℝ) / (d : ℝ) + 11 * (d : ℝ) *
      (n : ℝ) ^ ((2 * (d : ℝ) - 4) / (2 * (d : ℝ) - 3)) *
      (k : ℝ) ^ (((d : ℝ) - 1) / (2 * (d : ℝ) - 3)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [mul_assoc (11 * _), exps e n k hn0 hk0]
  set u := (n : ℝ) ^ (1 / ((2 * e + 1 : ℕ) : ℝ)) with hu
  set v := (k : ℝ) ^ (1 / ((2 * e + 1 : ℕ) : ℝ)) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0 _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hk0 _
  have hun : u ^ (2 * e + 1) = n := root_pow _ hn0 _ (by omega)
  have hvk : v ^ (2 * e + 1) = k := root_pow _ hk0 _ (by omega)
  have hd : (0 : ℝ) < ((e + 2 : ℕ) : ℝ) := by positivity
  have hnd : 0 ≤ (n : ℝ) / ((e + 2 : ℕ) : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero] at hnd ⊢
    have : 0 ≤ 11 * ((e + 2 : ℕ) : ℝ) * (u ^ (2 * e) * v ^ (e + 1)) := by positivity
    linarith
  · have huv : u ≤ v := by
      apply le_of_pow_le_pow_left₀ (n := 2 * e + 1) (by omega) hv0
      rw [hun, hvk]; exact_mod_cast hnk
    have hu1 : 1 ≤ u := by
      apply le_of_pow_le_pow_left₀ (n := 2 * e + 1) (by omega) hu0
      rw [hun, one_pow]; exact_mod_cast hpos
    have hv1 : 1 ≤ v := hu1.trans huv
    have h1 : (n : ℝ) ≤ u ^ (2 * e) * v ^ (e + 1) := by
      rw [← hun, pow_succ]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact huv.trans (le_self_pow₀ hv1 (by omega))
    have h2 : u ^ (2 * e) * v ^ (e + 1) ≤ 11 * ((e + 2 : ℕ) : ℝ) * (u ^ (2 * e) * v ^ (e + 1)) := by
      have : (1 : ℝ) ≤ 11 * ((e + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg e : (0:ℝ) ≤ e)]
      nlinarith [one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu1 (n := 2 * e))
        (one_le_pow₀ hv1 (n := e + 1))]
    linarith

end OnlineColoringKYY.Supplement.Dev.T515.PartR
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T515
open Classical OnlineColoringKYY.Supplement
alias trivial_range := OnlineColoringKYY.Supplement.Dev.T515.PartR.trivial_range

end OnlineColoringKYY.Supplement.Dev.T515
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement
open OnlineColoringKYY.Supplement.Dev.T515 in
theorem chk_theorem_5_15 (d : ℕ) (hd : 2 ≤ d) :
    ∀ n k : ℕ, ∃ θ : ℕ → ℕ, (∀ i, 1 ≤ i → i ≤ d - 1 → 1 ≤ θ i) ∧
      ∀ (G : SimpleGraph (Fin n)), G.Colorable k →
        expColors (dLevelRun d θ G n le_rfl) ≤
          ENNReal.ofReal ((n : ℝ) / (d : ℝ) + 11 * (d : ℝ) *
            (n : ℝ) ^ ((2 * (d : ℝ) - 4) / (2 * (d : ℝ) - 3)) *
            (k : ℝ) ^(((d : ℝ) - 1) / (2 * (d : ℝ) - 3))) := by
  intro n k
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  by_cases hk : 1 ≤ k ∧ k < n
  · obtain ⟨θ, m₀, hθ, htail, harith⟩ := params d hd n k hk.1 hk.2
    refine ⟨θ, hθ, fun G hG => ?_⟩
    have hE := expColors_le d hd θ hθ G hG m₀ htail
    set N : ℕ := n + (d - 1) * (k * θ 1) + ∑ t ∈ Finset.Icc 2 (d - 1), (d - t) * (m₀ t + 2)
    have h1 : expColors (dLevelRun d θ G n le_rfl) ≤ ENNReal.ofReal ((N : ℝ) / d) := by
      rw [ENNReal.ofReal_div_of_pos hd0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      rw [ENNReal.le_div_iff_mul_le (by simp; omega) (by simp)]
      rw [mul_comm]; exact hE
    exact h1.trans (ENNReal.ofReal_le_ofReal harith)
  · refine ⟨fun _ => 1, fun _ _ _ => le_rfl, fun G hG => ?_⟩
    refine (expColors_le_n d _ G).trans ?_
    have hnk : n ≤ k := by
      by_cases hk0 : k = 0
      · subst hk0
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · exfalso
          obtain ⟨C⟩ := hG
          exact (C ⟨0, hn⟩).elim0
      · simp only [not_and, not_lt] at hk; exact hk (by omega)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (trivial_range d hd n k hnk)

end OnlineColoringKYY.Supplement
end

theorem solution : type_of% @OnlineColoringKYY.Supplement.chk_theorem_5_15 := @OnlineColoringKYY.Supplement.chk_theorem_5_15
