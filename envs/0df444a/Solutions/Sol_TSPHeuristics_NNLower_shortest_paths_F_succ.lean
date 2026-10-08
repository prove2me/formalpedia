-- Prove2me | solution 1 for TSPHeuristics.NNLower.shortest_paths_F_succ
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:49:54.396648+00:00
-- url     : https://prove2.me/submissions/64c7c06f-1949-483c-8d15-93406f2516dc

import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily
import Mathlib

namespace TSPSP
open TSPHeuristics.NNLower

/-! ### Walks and shortest-path distances -/

theorem walk_single {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {w : ℝ}
    (he : (x, y, w) ∈ E ∨ (y, x, w) ∈ E) : WalkCost E x y w := by
  simpa using WalkCost.cons he (WalkCost.nil y)

theorem walk_trans {E : List (ℕ × ℕ × ℝ)} {x y z : ℕ} {c₁ c₂ : ℝ}
    (h₁ : WalkCost E x y c₁) (h₂ : WalkCost E y z c₂) : WalkCost E x z (c₁ + c₂) := by
  induction h₁ with
  | nil x => simpa using h₂
  | cons he h ih =>
    have := WalkCost.cons he (ih h₂)
    simpa [add_assoc] using this

theorem walk_symm {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {c : ℝ} (h : WalkCost E x y c) :
    WalkCost E y x c := by
  induction h with
  | nil x => exact WalkCost.nil x
  | cons he h ih =>
    have := walk_trans ih (walk_single he.symm)
    simpa [add_comm] using this

theorem walk_mono {E E' : List (ℕ × ℕ × ℝ)} (h : ∀ e ∈ E, e ∈ E') {x y : ℕ} {c : ℝ}
    (hw : WalkCost E x y c) : WalkCost E' x y c := by
  induction hw with
  | nil x => exact WalkCost.nil x
  | cons he _ ih =>
    refine WalkCost.cons ?_ ih
    rcases he with he | he
    · exact Or.inl (h _ he)
    · exact Or.inr (h _ he)

theorem walk_shift (k : ℕ) {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {c : ℝ} (hw : WalkCost E x y c) :
    WalkCost (E.map fun e => (e.1 + k, e.2.1 + k, e.2.2)) (x + k) (y + k) c := by
  induction hw with
  | nil x => exact WalkCost.nil _
  | cons he _ ih =>
    refine WalkCost.cons ?_ ih
    rcases he with he | he
    · exact Or.inl (List.mem_map.mpr ⟨_, he, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨_, he, rfl⟩)

/-- All edge weights nonnegative. -/
def NN (E : List (ℕ × ℕ × ℝ)) : Prop := ∀ e ∈ E, 0 ≤ e.2.2

theorem walk_nonneg {E : List (ℕ × ℕ × ℝ)} (hE : NN E) {x y : ℕ} {c : ℝ}
    (hw : WalkCost E x y c) : 0 ≤ c := by
  induction hw with
  | nil x => exact le_refl _
  | @cons x y z w c he _ ih =>
    have hw0 : 0 ≤ w := by
      rcases he with he | he
      · exact hE _ he
      · exact hE _ he
    linarith

theorem spDist_le {E : List (ℕ × ℕ × ℝ)} (hE : NN E) {x y : ℕ} {c : ℝ}
    (hw : WalkCost E x y c) : spDist E x y ≤ c :=
  csInf_le ⟨0, fun _ h => walk_nonneg hE h⟩ hw

theorem le_spDist {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {c₀ t : ℝ} (hw : WalkCost E x y c₀)
    (h : ∀ c, WalkCost E x y c → t ≤ c) : t ≤ spDist E x y :=
  le_csInf ⟨c₀, hw⟩ h

theorem spDist_symm (E : List (ℕ × ℕ × ℝ)) (x y : ℕ) : spDist E x y = spDist E y x := by
  unfold spDist
  congr 1
  ext c
  exact ⟨walk_symm, walk_symm⟩

theorem spDist_self {E : List (ℕ × ℕ × ℝ)} (hE : NN E) (x : ℕ) : spDist E x x = 0 := by
  refine le_antisymm (spDist_le hE (WalkCost.nil x)) ?_
  exact le_spDist (WalkCost.nil x) fun c hc => walk_nonneg hE hc

theorem spDist_triangle {E : List (ℕ × ℕ × ℝ)} (hE : NN E) {x y z : ℕ} {c₁ c₂ : ℝ}
    (h₁ : WalkCost E x y c₁) (h₂ : WalkCost E y z c₂) :
    spDist E x z ≤ spDist E x y + spDist E y z := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hb₁ : BddBelow {c : ℝ | WalkCost E x y c} := ⟨0, fun _ h => walk_nonneg hE h⟩
  have hb₂ : BddBelow {c : ℝ | WalkCost E y z c} := ⟨0, fun _ h => walk_nonneg hE h⟩
  obtain ⟨a, ha, ha'⟩ := exists_lt_of_csInf_lt (s := {c : ℝ | WalkCost E x y c}) ⟨c₁, h₁⟩
    (show spDist E x y < spDist E x y + ε / 2 by linarith)
  obtain ⟨b, hb, hb'⟩ := exists_lt_of_csInf_lt (s := {c : ℝ | WalkCost E y z c}) ⟨c₂, h₂⟩
    (show spDist E y z < spDist E y z + ε / 2 by linarith)
  have := spDist_le hE (walk_trans ha hb)
  linarith

/-- A function that is `w`-Lipschitz along every edge bounds the cost of every walk. -/
theorem lip_walk {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ}
    (hφ : ∀ e ∈ E, |φ e.1 - φ e.2.1| ≤ e.2.2) {x y : ℕ} {c : ℝ} (hw : WalkCost E x y c) :
    φ y - φ x ≤ c := by
  induction hw with
  | nil x => simp
  | @cons x y z w c he _ ih =>
    have : φ y - φ x ≤ w := by
      rcases he with he | he
      · have := hφ _ he
        simp only at this
        have := (abs_le.mp this).1
        linarith
      · have := hφ _ he
        simp only at this
        have := (abs_le.mp this).2
        linarith
    linarith

theorem lower_of_lip {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ}
    (hφ : ∀ e ∈ E, |φ e.1 - φ e.2.1| ≤ e.2.2) {x y : ℕ} {c₀ : ℝ} (hw : WalkCost E x y c₀) :
    φ y - φ x ≤ spDist E x y :=
  le_spDist hw fun _ hc => lip_walk hφ hc

theorem spDist_edge {E : List (ℕ × ℕ × ℝ)} (hE : NN E) {x y : ℕ} {w : ℝ}
    (he : (x, y, w) ∈ E ∨ (y, x, w) ∈ E) : spDist E x y ≤ w :=
  spDist_le hE (walk_single he)

/-! ### Arithmetic of the family -/

theorem numNodes_succ (j : ℕ) : numNodes (j + 1) = 2 * numNodes j + 1 := by
  unfold numNodes
  have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
  omega

theorem middle_lt (j : ℕ) : middle j < numNodes j := by
  unfold middle numNodes
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  omega

theorem numNodes_ge (j : ℕ) (hj : 1 ≤ j) : 3 ≤ numNodes j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [numNodes_succ]
  unfold numNodes
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  omega

theorem ell_ge_one (j : ℕ) : 1 ≤ ell j := by
  unfold ell
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2 : (-1 : ℝ) ^ j ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ j with h | h <;> simp [h]
  linarith

theorem ell_rel (j : ℕ) (hj : 1 ≤ j) :
    ell (j + 2) = ell (j + 1) + 2 * ell j - 1 ∧ ell (j + 1) ≤ 2 * ell j ∧
      2 * ell j - 1 ≤ ell (j + 1) ∧ 2 ≤ ell j := by
  have hp : (-1 : ℝ) ^ j = 1 ∨ (-1 : ℝ) ^ j = -1 := neg_one_pow_eq_or ℝ j
  have h1 : ell (j + 1) = (4 * 2 * 2 ^ j + (-1) ^ j + 3) / 6 := by
    unfold ell; rw [pow_succ, pow_succ]; ring
  have h2 : ell (j + 2) = (4 * 4 * 2 ^ j - (-1) ^ j + 3) / 6 := by
    unfold ell; rw [pow_succ, pow_succ, pow_succ, pow_succ]; ring
  have hq : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hq4 : (-1 : ℝ) ^ j = 1 → (4 : ℝ) ≤ 2 ^ j := by
    intro h
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have : j = 1 := by omega
      subst this
      norm_num at h
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj2
  have h0 : ell j = (4 * 2 ^ j - (-1) ^ j + 3) / 6 := rfl
  rcases hp with h | h
  · have := hq4 h
    rw [h0, h1, h2, h]
    refine ⟨by ring, by linarith, by linarith, by linarith⟩
  · rw [h0, h1, h2, h]
    refine ⟨by ring, by linarith, by linarith, by linarith⟩

/-! ### Structure of `F_i` -/

theorem edgesF_succ (j : ℕ) (hj : 1 ≤ j) :
    edgesF (j + 1) =
      edgesF j ++
        (edgesF j).map (fun e => (e.1 + (numNodes j + 1), e.2.1 + (numNodes j + 1), e.2.2)) ++
      [(numNodes j - 1, numNodes j, 1),
       (numNodes j, numNodes j + 1, 1),
       (numNodes j, numNodes j + 1 + middle j, ell j),
       (middle j, numNodes j + 1, ell j)] := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rfl

theorem edgesF_nn : ∀ j, NN (edgesF j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => intro e he; simp [edgesF] at he
    | 1 => intro e he; simp [edgesF] at he; rcases he with rfl | rfl | rfl <;> norm_num
    | k + 2 =>
      intro e he
      rw [edgesF_succ (k + 1) (by omega)] at he
      simp only [List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with (he | ⟨e', he', rfl⟩) | he | he | he | he
      · exact ih (k + 1) (by omega) e he
      · exact ih (k + 1) (by omega) e' he'
      · rw [he]; norm_num
      · rw [he]; norm_num
      · rw [he]; exact (by linarith [ell_ge_one (k + 1)])
      · rw [he]; exact (by linarith [ell_ge_one (k + 1)])

theorem edgesF_lt : ∀ j, 1 ≤ j → ∀ e ∈ edgesF j, e.1 < numNodes j ∧ e.2.1 < numNodes j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro e he; simp [edgesF, numNodes] at he ⊢; rcases he with rfl | rfl | rfl <;> simp
  | succ k hk ih =>
    intro e he
    rw [edgesF_succ k hk] at he
    have hs := numNodes_succ k
    have hm := middle_lt k
    have h3 := numNodes_ge k hk
    simp only [List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with (he | ⟨e', he', rfl⟩) | he | he | he | he
    · have := ih e he; omega
    · have := ih e' he'; simp only; omega
    · rw [he]; simp only; omega
    · rw [he]; simp only; omega
    · rw [he]; simp only; omega
    · rw [he]; simp only; omega

theorem spDist_le_of_embed {E E' : List (ℕ × ℕ × ℝ)} (hE' : NN E') {x y x' y' : ℕ} {c₀ : ℝ}
    (hw : WalkCost E x y c₀) (hemb : ∀ c, WalkCost E x y c → WalkCost E' x' y' c) :
    spDist E' x' y' ≤ spDist E x y :=
  csInf_le_csInf ⟨0, fun _ h => walk_nonneg hE' h⟩ ⟨c₀, hw⟩ hemb

/-! ### Connectivity of `F_j` -/

theorem edgesF_sub_succ (j : ℕ) (hj : 1 ≤ j) : ∀ e ∈ edgesF j, e ∈ edgesF (j + 1) := by
  intro e he
  rw [edgesF_succ j hj]
  exact List.mem_append_left _ (List.mem_append_left _ he)

theorem edgesF_shift_sub (j : ℕ) (hj : 1 ≤ j) :
    ∀ e ∈ (edgesF j).map (fun e => (e.1 + (numNodes j + 1), e.2.1 + (numNodes j + 1), e.2.2)),
      e ∈ edgesF (j + 1) := by
  intro e he
  rw [edgesF_succ j hj]
  exact List.mem_append_left _ (List.mem_append_right _ he)

theorem edge_CD (j : ℕ) (hj : 1 ≤ j) : (numNodes j - 1, numNodes j, (1 : ℝ)) ∈ edgesF (j + 1) := by
  rw [edgesF_succ j hj]; simp

theorem edge_DE (j : ℕ) (hj : 1 ≤ j) : (numNodes j, numNodes j + 1, (1 : ℝ)) ∈ edgesF (j + 1) := by
  rw [edgesF_succ j hj]; simp

theorem edge_DF (j : ℕ) (hj : 1 ≤ j) :
    (numNodes j, numNodes j + 1 + middle j, ell j) ∈ edgesF (j + 1) := by
  rw [edgesF_succ j hj]; simp

theorem edge_BE (j : ℕ) (hj : 1 ≤ j) :
    (middle j, numNodes j + 1, ell j) ∈ edgesF (j + 1) := by
  rw [edgesF_succ j hj]; simp

theorem reach0 : ∀ j, 1 ≤ j → ∀ v, v < numNodes j → ∃ c, WalkCost (edgesF j) 0 v c := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro v hv
    have : v = 0 ∨ v = 1 ∨ v = 2 := by simp [numNodes] at hv; omega
    rcases this with rfl | rfl | rfl
    · exact ⟨0, WalkCost.nil 0⟩
    · exact ⟨1, walk_single (Or.inl (by simp [edgesF]))⟩
    · exact ⟨1, walk_single (Or.inl (by simp [edgesF]))⟩
  | succ k hk ih =>
    intro v hv
    have hs := numNodes_succ k
    have h3 := numNodes_ge k hk
    have hD : ∃ c, WalkCost (edgesF (k + 1)) 0 (numNodes k) c := by
      obtain ⟨c, hc⟩ := ih (numNodes k - 1) (by omega)
      exact ⟨c + 1, walk_trans (walk_mono (edgesF_sub_succ k hk) hc)
        (walk_single (Or.inl (edge_CD k hk)))⟩
    by_cases h1 : v < numNodes k
    · obtain ⟨c, hc⟩ := ih v h1
      exact ⟨c, walk_mono (edgesF_sub_succ k hk) hc⟩
    · by_cases h2 : v = numNodes k
      · subst h2; exact hD
      · obtain ⟨u, rfl⟩ : ∃ u, v = u + (numNodes k + 1) := ⟨v - (numNodes k + 1), by omega⟩
        obtain ⟨c, hc⟩ := ih u (by omega)
        obtain ⟨c₀, h0⟩ := hD
        have hE : WalkCost (edgesF (k + 1)) (numNodes k) (numNodes k + 1) 1 :=
          walk_single (Or.inl (edge_DE k hk))
        have := walk_shift (numNodes k + 1) hc
        simp only [zero_add] at this
        exact ⟨c₀ + 1 + c, walk_trans (walk_trans h0 hE) (walk_mono (edgesF_shift_sub k hk) this)⟩

theorem conn (j : ℕ) (hj : 1 ≤ j) {u v : ℕ} (hu : u < numNodes j) (hv : v < numNodes j) :
    ∃ c, WalkCost (edgesF j) u v c := by
  obtain ⟨c₁, h₁⟩ := reach0 j hj u hu
  obtain ⟨c₂, h₂⟩ := reach0 j hj v hv
  exact ⟨c₁ + c₂, walk_trans (walk_symm h₁) h₂⟩

theorem dtri (j : ℕ) (hj : 1 ≤ j) {u v w : ℕ} (hu : u < numNodes j) (hv : v < numNodes j)
    (hw : w < numNodes j) :
    spDist (edgesF j) u w ≤ spDist (edgesF j) u v + spDist (edgesF j) v w := by
  obtain ⟨c₁, h₁⟩ := conn j hj hu hv
  obtain ⟨c₂, h₂⟩ := conn j hj hv hw
  exact spDist_triangle (edgesF_nn j) h₁ h₂

/-- The profile of `F_j`: distances among its start, middle and right nodes. -/
def Pr (j : ℕ) : Prop :=
  spDist (edgesF j) 0 (middle j) = ell j - 1 ∧
  spDist (edgesF j) (middle j) (numNodes j - 1) = ell j - 1 ∧
  spDist (edgesF j) 0 (numNodes j - 1) = ell (j + 1) - 2

/-- Extension of boundary values on `{0, m, s - 1}` to a `d_j`-Lipschitz function. -/
noncomputable def psi (j : ℕ) (h0 hm hr : ℝ) (v : ℕ) : ℝ :=
  min (h0 + spDist (edgesF j) 0 v)
    (min (hm + spDist (edgesF j) (middle j) v) (hr + spDist (edgesF j) (numNodes j - 1) v))

theorem psi_vals (j : ℕ) (_hj : 1 ≤ j) (hpr : Pr j) (h0 hm hr : ℝ)
    (c1 : |h0 - hm| ≤ ell j - 1) (c2 : |hm - hr| ≤ ell j - 1) (c3 : |h0 - hr| ≤ ell (j + 1) - 2) :
    psi j h0 hm hr 0 = h0 ∧ psi j h0 hm hr (middle j) = hm ∧
      psi j h0 hm hr (numNodes j - 1) = hr := by
  obtain ⟨p1, p2, p3⟩ := hpr
  have hnn := edgesF_nn j
  have s0 := spDist_self hnn 0
  have sm := spDist_self hnn (middle j)
  have sr := spDist_self hnn (numNodes j - 1)
  have y1 := spDist_symm (edgesF j) (middle j) 0
  have y2 := spDist_symm (edgesF j) (numNodes j - 1) (middle j)
  have y3 := spDist_symm (edgesF j) (numNodes j - 1) 0
  have a1 := abs_le.mp c1
  have a2 := abs_le.mp c2
  have a3 := abs_le.mp c3
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm ?_ (le_min ?_ (le_min ?_ ?_))
    · calc _ ≤ h0 + spDist (edgesF j) 0 0 := min_le_left _ _
        _ = h0 := by rw [s0]; ring
    · linarith
    · linarith
    · linarith
  · refine le_antisymm ?_ (le_min ?_ (le_min ?_ ?_))
    · calc _ ≤ hm + spDist (edgesF j) (middle j) (middle j) :=
            (min_le_right _ _).trans (min_le_left _ _)
        _ = hm := by rw [sm]; ring
    · linarith
    · linarith
    · linarith
  · refine le_antisymm ?_ (le_min ?_ (le_min ?_ ?_))
    · calc _ ≤ hr + spDist (edgesF j) (numNodes j - 1) (numNodes j - 1) :=
            (min_le_right _ _).trans (min_le_right _ _)
        _ = hr := by rw [sr]; ring
    · linarith
    · linarith
    · linarith

theorem psi_lip (j : ℕ) (hj : 1 ≤ j) (h0 hm hr : ℝ) {u v : ℕ} (hu : u < numNodes j)
    (hv : v < numNodes j) :
    |psi j h0 hm hr u - psi j h0 hm hr v| ≤ spDist (edgesF j) u v := by
  have h3 := numNodes_ge j hj
  have hmid := middle_lt j
  have key : ∀ u v : ℕ, u < numNodes j → v < numNodes j →
      psi j h0 hm hr u - spDist (edgesF j) v u ≤ psi j h0 hm hr v := by
    intro u v hu hv
    unfold psi
    refine le_min ?_ (le_min ?_ ?_)
    · have t := dtri j hj (u := 0) (v := v) (w := u) (by omega) hv hu
      have := (min_le_left _ _ : min (h0 + spDist (edgesF j) 0 u)
        (min (hm + spDist (edgesF j) (middle j) u) (hr + spDist (edgesF j) (numNodes j - 1) u))
        ≤ h0 + spDist (edgesF j) 0 u)
      linarith
    · have t := dtri j hj (u := middle j) (v := v) (w := u) hmid hv hu
      have := ((min_le_right _ _).trans (min_le_left _ _) :
        min (h0 + spDist (edgesF j) 0 u)
        (min (hm + spDist (edgesF j) (middle j) u) (hr + spDist (edgesF j) (numNodes j - 1) u))
        ≤ hm + spDist (edgesF j) (middle j) u)
      linarith
    · have t := dtri j hj (u := numNodes j - 1) (v := v) (w := u) (by omega) hv hu
      have := ((min_le_right _ _).trans (min_le_right _ _) :
        min (h0 + spDist (edgesF j) 0 u)
        (min (hm + spDist (edgesF j) (middle j) u) (hr + spDist (edgesF j) (numNodes j - 1) u))
        ≤ hr + spDist (edgesF j) (numNodes j - 1) u)
      linarith
  have k1 := key u v hu hv
  have k2 := key v u hv hu
  have sy := spDist_symm (edgesF j) u v
  rw [abs_le]
  constructor <;> linarith

/-- Gluing: boundary values on the seven named nodes of `F_{j+1}`, compatible with the profile of
`F_j` and the connecting edges, extend to a Lipschitz function on all of `F_{j+1}`. -/
theorem glue (j : ℕ) (hj : 1 ≤ j) (hpr : Pr j) (hA hB hC hD hE hF hG : ℝ)
    (c1 : |hA - hB| ≤ ell j - 1) (c2 : |hB - hC| ≤ ell j - 1) (c3 : |hA - hC| ≤ ell (j + 1) - 2)
    (c4 : |hE - hF| ≤ ell j - 1) (c5 : |hF - hG| ≤ ell j - 1) (c6 : |hE - hG| ≤ ell (j + 1) - 2)
    (c7 : |hC - hD| ≤ 1) (c8 : |hD - hE| ≤ 1) (c9 : |hD - hF| ≤ ell j)
    (c10 : |hB - hE| ≤ ell j) :
    ∃ φ : ℕ → ℝ, (∀ e ∈ edgesF (j + 1), |φ e.1 - φ e.2.1| ≤ e.2.2) ∧
      φ 0 = hA ∧ φ (middle j) = hB ∧ φ (numNodes j - 1) = hC ∧ φ (numNodes j) = hD ∧
      φ (numNodes j + 1) = hE ∧ φ (numNodes j + 1 + middle j) = hF ∧
      φ (2 * numNodes j) = hG := by
  have h3 := numNodes_ge j hj
  have hmid := middle_lt j
  obtain ⟨l0, lm, lr⟩ := psi_vals j hj hpr hA hB hC c1 c2 c3
  obtain ⟨r0, rm, rr⟩ := psi_vals j hj hpr hE hF hG c4 c5 c6
  set s := numNodes j with hs
  set φ : ℕ → ℝ := fun v =>
    if v < s then psi j hA hB hC v else if v = s then hD else psi j hE hF hG (v - (s + 1))
    with hφ
  have eL : ∀ v, v < s → φ v = psi j hA hB hC v := fun v hv => by simp [hφ, hv]
  have eD : φ s = hD := by simp [hφ]
  have eR : ∀ u, φ (u + (s + 1)) = psi j hE hF hG u := fun u => by
    have h1 : ¬ (u + (s + 1) < s) := by omega
    have h2 : u + (s + 1) ≠ s := by omega
    simp [hφ, h1, h2]
  refine ⟨φ, ?_, ?_, ?_, ?_, eD, ?_, ?_, ?_⟩
  · intro e he
    rw [edgesF_succ j hj] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (he | ⟨e', he', rfl⟩) | he | he | he | he
    · obtain ⟨a, b, w⟩ := e
      obtain ⟨ha, hb⟩ := edgesF_lt j hj _ he
      simp only at ha hb ⊢
      rw [eL a ha, eL b hb]
      exact (psi_lip j hj hA hB hC ha hb).trans
        (spDist_edge (edgesF_nn j) (Or.inl he))
    · obtain ⟨a, b, w⟩ := e'
      simp only
      rw [eR a, eR b]
      exact (psi_lip j hj hE hF hG (edgesF_lt j hj _ he').1 (edgesF_lt j hj _ he').2).trans
        (spDist_edge (edgesF_nn j) (Or.inl he'))
    · rw [he]; simp only
      rw [eL (s - 1) (by omega), eD, lr]; simpa using c7
    · rw [he]; simp only
      have := eR 0
      rw [zero_add] at this
      rw [eD, this, r0]; simpa using c8
    · rw [he]; simp only
      have := eR (middle j)
      rw [add_comm] at this
      rw [eD, this, rm]; simpa using c9
    · rw [he]; simp only
      have := eR 0
      rw [zero_add] at this
      rw [eL (middle j) hmid, this, lm, r0]; simpa using c10
  · rw [eL 0 (by omega), l0]
  · rw [eL _ hmid, lm]
  · rw [eL _ (by omega), lr]
  · have := eR 0
    rw [zero_add] at this
    rw [this, r0]
  · have := eR (middle j)
    rw [add_comm] at this
    rw [this, rm]
  · have := eR (s - 1)
    have h2 : s - 1 + (s + 1) = 2 * s := by omega
    rw [h2] at this
    rw [this, rr]

theorem shift_emb (j : ℕ) (hj : 1 ≤ j) {x y : ℕ} {c : ℝ} (h : WalkCost (edgesF j) x y c) :
    WalkCost (edgesF (j + 1)) (x + (numNodes j + 1)) (y + (numNodes j + 1)) c :=
  walk_mono (edgesF_shift_sub j hj) (walk_shift (numNodes j + 1) h)

/-- Eqs. (2.13)-(2.17) for `F_{j+1}`, given the profile of `F_j`. -/
theorem step (j : ℕ) (hj : 1 ≤ j) (hpr : Pr j) :
    (spDist (edgesF (j + 1)) 0 (middle j) = ell j - 1 ∧
      spDist (edgesF (j + 1)) (middle j) (numNodes j - 1) = ell j - 1 ∧
      spDist (edgesF (j + 1)) (numNodes j + 1) (numNodes j + 1 + middle j) = ell j - 1 ∧
      spDist (edgesF (j + 1)) (numNodes j + 1 + middle j) (2 * numNodes j) = ell j - 1) ∧
    (spDist (edgesF (j + 1)) 0 (numNodes j - 1) = ell (j + 1) - 2 ∧
      spDist (edgesF (j + 1)) (numNodes j + 1) (2 * numNodes j) = ell (j + 1) - 2) ∧
    (spDist (edgesF (j + 1)) (middle j) (numNodes j + 1) = ell j ∧
      spDist (edgesF (j + 1)) (numNodes j) (numNodes j + 1 + middle j) = ell j) ∧
    (spDist (edgesF (j + 1)) 0 (numNodes j) = ell (j + 1) - 1 ∧
      spDist (edgesF (j + 1)) (numNodes j) (2 * numNodes j) = ell (j + 1) - 1) ∧
    spDist (edgesF (j + 1)) 0 (2 * numNodes j) = ell (j + 2) - 2 := by
  obtain ⟨hrel, hb1, hb2, ha2⟩ := ell_rel j hj
  obtain ⟨p1, p2, p3⟩ := hpr
  have hN : numNodes (j + 1) = 2 * numNodes j + 1 := numNodes_succ j
  have hmid := middle_lt j
  have h3 := numNodes_ge j hj
  set s := numNodes j with hs
  set m := middle j with hm
  set a := ell j with ha
  set b := ell (j + 1) with hb
  set c := ell (j + 2) with hc
  have hnn := edgesF_nn (j + 1)
  have W : ∀ u v : ℕ, u < 2 * s + 1 → v < 2 * s + 1 → ∃ c, WalkCost (edgesF (j + 1)) u v c :=
    fun u v hu hv => conn (j + 1) (by omega) (by omega) (by omega)
  have low : ∀ (φ : ℕ → ℝ), (∀ e ∈ edgesF (j + 1), |φ e.1 - φ e.2.1| ≤ e.2.2) →
      ∀ x y : ℕ, x < 2 * s + 1 → y < 2 * s + 1 → φ y - φ x ≤ spDist (edgesF (j + 1)) x y := by
    intro φ hφ x y hx hy
    obtain ⟨c₀, hw⟩ := W x y hx hy
    exact lower_of_lip hφ hw
  have tri : ∀ x y z : ℕ, x < 2 * s + 1 → y < 2 * s + 1 → z < 2 * s + 1 →
      spDist (edgesF (j + 1)) x z ≤ spDist (edgesF (j + 1)) x y + spDist (edgesF (j + 1)) y z := by
    intro x y z hx hy hz
    obtain ⟨c₁, h₁⟩ := W x y hx hy
    obtain ⟨c₂, h₂⟩ := W y z hy hz
    exact spDist_triangle hnn h₁ h₂
  -- upper bounds
  have embL : ∀ x y : ℕ, x < s → y < s →
      spDist (edgesF (j + 1)) x y ≤ spDist (edgesF j) x y := by
    intro x y hx hy
    obtain ⟨c₀, hw⟩ := conn j hj hx hy
    exact spDist_le_of_embed hnn hw fun c h => walk_mono (edgesF_sub_succ j hj) h
  have embR : ∀ x y : ℕ, x < s → y < s →
      spDist (edgesF (j + 1)) (x + (s + 1)) (y + (s + 1)) ≤ spDist (edgesF j) x y := by
    intro x y hx hy
    obtain ⟨c₀, hw⟩ := conn j hj hx hy
    exact spDist_le_of_embed hnn hw fun c h => shift_emb j hj h
  have uAB : spDist (edgesF (j + 1)) 0 m ≤ a - 1 := by
    have := embL 0 m (by omega) hmid; linarith
  have uBC : spDist (edgesF (j + 1)) m (s - 1) ≤ a - 1 := by
    have := embL m (s - 1) hmid (by omega); linarith
  have uAC : spDist (edgesF (j + 1)) 0 (s - 1) ≤ b - 2 := by
    have := embL 0 (s - 1) (by omega) (by omega); linarith
  have uEF : spDist (edgesF (j + 1)) (s + 1) (s + 1 + m) ≤ a - 1 := by
    have := embR 0 m (by omega) hmid
    rw [show 0 + (s + 1) = s + 1 by omega, show m + (s + 1) = s + 1 + m by omega] at this
    linarith
  have uFG : spDist (edgesF (j + 1)) (s + 1 + m) (2 * s) ≤ a - 1 := by
    have := embR m (s - 1) hmid (by omega)
    rw [show m + (s + 1) = s + 1 + m by omega, show s - 1 + (s + 1) = 2 * s by omega] at this
    linarith
  have uEG : spDist (edgesF (j + 1)) (s + 1) (2 * s) ≤ b - 2 := by
    have := embR 0 (s - 1) (by omega) (by omega)
    rw [show 0 + (s + 1) = s + 1 by omega, show s - 1 + (s + 1) = 2 * s by omega] at this
    linarith
  have uBE : spDist (edgesF (j + 1)) m (s + 1) ≤ a :=
    spDist_edge hnn (Or.inl (edge_BE j hj))
  have uDF : spDist (edgesF (j + 1)) s (s + 1 + m) ≤ a :=
    spDist_edge hnn (Or.inl (edge_DF j hj))
  have uCD : spDist (edgesF (j + 1)) (s - 1) s ≤ 1 :=
    spDist_edge hnn (Or.inl (edge_CD j hj))
  have uDE : spDist (edgesF (j + 1)) s (s + 1) ≤ 1 :=
    spDist_edge hnn (Or.inl (edge_DE j hj))
  have uAD : spDist (edgesF (j + 1)) 0 s ≤ b - 1 := by
    have := tri 0 (s - 1) s (by omega) (by omega) (by omega)
    linarith
  have uDG : spDist (edgesF (j + 1)) s (2 * s) ≤ b - 1 := by
    have := tri s (s + 1) (2 * s) (by omega) (by omega) (by omega)
    linarith
  have uAG : spDist (edgesF (j + 1)) 0 (2 * s) ≤ c - 2 := by
    have t1 := tri 0 (s + 1) (2 * s) (by omega) (by omega) (by omega)
    have t2 := tri 0 m (s + 1) (by omega) (by omega) (by omega)
    linarith
  -- lower bounds: four extensions
  obtain ⟨φA, lA, a0, am, ar, aD, aE, aF, aG⟩ := glue j hj ⟨p1, p2, p3⟩
    0 (a - 1) (b - 2) (b - 1) (2 * a - 1) (3 * a - 2) (c - 2)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨φC, lC, c0, cm, cr, cD, cE, cF, cG⟩ := glue j hj ⟨p1, p2, p3⟩
    (b - 2) (a - 1) 0 1 2 (a + 1) b
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨φF, lF, f0, fm, fr, fD, fE, fF, fG⟩ := glue j hj ⟨p1, p2, p3⟩
    (3 * a - 2) (2 * a - 1) (a + 1) a (a - 1) 0 (a - 1)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨φG, lG, g0, gm, gr, gD, gE, gF, gG⟩ := glue j hj ⟨p1, p2, p3⟩
    (c - 2) (a + b - 2) b (b - 1) (b - 2) (a - 1) 0
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
  have sy : ∀ x y : ℕ, spDist (edgesF (j + 1)) x y = spDist (edgesF (j + 1)) y x :=
    fun x y => spDist_symm _ x y
  -- A-vector
  have kAB := low φA lA 0 m (by omega) (by omega)
  have kAC := low φA lA 0 (s - 1) (by omega) (by omega)
  have kAD := low φA lA 0 s (by omega) (by omega)
  have kAG := low φA lA 0 (2 * s) (by omega) (by omega)
  have kBE := low φA lA m (s + 1) (by omega) (by omega)
  rw [a0, am] at kAB
  rw [a0, ar] at kAC
  rw [a0, aD] at kAD
  rw [a0, aG] at kAG
  rw [am, aE] at kBE
  -- C-vector (flip)
  have kCB := low φC lC (s - 1) m (by omega) (by omega)
  rw [cr, cm] at kCB
  rw [sy (s - 1) m] at kCB
  -- F-vector
  have kFE := low φF lF (s + 1 + m) (s + 1) (by omega) (by omega)
  have kFG := low φF lF (s + 1 + m) (2 * s) (by omega) (by omega)
  have kFD := low φF lF (s + 1 + m) s (by omega) (by omega)
  rw [fF, fE] at kFE
  rw [fF, fG] at kFG
  rw [fF, fD] at kFD
  rw [sy (s + 1 + m) (s + 1)] at kFE
  rw [sy (s + 1 + m) s] at kFD
  -- G-vector
  have kGE := low φG lG (2 * s) (s + 1) (by omega) (by omega)
  have kGD := low φG lG (2 * s) s (by omega) (by omega)
  rw [gG, gE] at kGE
  rw [gG, gD] at kGD
  rw [sy (2 * s) (s + 1)] at kGE
  rw [sy (2 * s) s] at kGD
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-! ### The profile for all `j ≥ 1` -/

/-- Indicator potential on `F_1`. -/
noncomputable def ind (y v : ℕ) : ℝ := if v = y then 1 else 0

theorem ind_lip (y : ℕ) : ∀ e ∈ edgesF 1, |ind y e.1 - ind y e.2.1| ≤ e.2.2 := by
  intro e he
  simp only [edgesF, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp only [ind] <;> split_ifs <;> norm_num

theorem base_dist (x y : ℕ) (hx : x < 3) (hy : y < 3) (hxy : x ≠ y)
    (h : (x, y, (1 : ℝ)) ∈ edgesF 1 ∨ (y, x, (1 : ℝ)) ∈ edgesF 1) :
    spDist (edgesF 1) x y = 1 := by
  refine le_antisymm (spDist_edge (edgesF_nn 1) h) ?_
  obtain ⟨c₀, hw⟩ := conn 1 le_rfl (by simp [numNodes]; omega) (by simp [numNodes]; omega)
    (u := x) (v := y)
  have := lower_of_lip (ind_lip y) hw
  simp only [ind, if_true, hxy, if_false] at this
  linarith

theorem profile : ∀ j, 1 ≤ j → Pr j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have e1 : ell 1 = 2 := by unfold ell; norm_num
    have e2 : ell 2 = 3 := by unfold ell; norm_num
    have hm : middle 1 = 1 := by simp [middle]
    have hn : numNodes 1 - 1 = 2 := by simp [numNodes]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, e1, base_dist 0 1 (by omega) (by omega) (by omega) (Or.inl (by simp [edgesF]))]; norm_num
    · rw [hm, hn, e1, base_dist 1 2 (by omega) (by omega) (by omega) (Or.inl (by simp [edgesF]))]
      norm_num
    · rw [hn, e2, base_dist 0 2 (by omega) (by omega) (by omega) (Or.inl (by simp [edgesF]))]
      norm_num
  | succ k hk ih =>
    obtain ⟨⟨_, _, _, _⟩, ⟨_, _⟩, _, ⟨h4, h5⟩, h6⟩ := step k hk ih
    have hm : middle (k + 1) = numNodes k := by unfold middle numNodes; rfl
    have hn : numNodes (k + 1) - 1 = 2 * numNodes k := by rw [numNodes_succ]; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]; exact h4
    · rw [hm, hn]; exact h5
    · rw [hn]; exact h6

end TSPSP

open TSPHeuristics.NNLower in
theorem solution (i : ℕ) (hi : 1 ≤ i) :
    let s := numNodes i
    let A := 0
    let B := middle i
    let C := s - 1
    let D := s
    let E := s + 1
    let F := s + 1 + middle i
    let G := 2 * s
    let dF := spDist (edgesF (i + 1))
    (dF A B = ell i - 1 ∧ dF B C = ell i - 1 ∧ dF E F = ell i - 1 ∧ dF F G = ell i - 1) ∧
    (dF A C = ell (i + 1) - 2 ∧ dF E G = ell (i + 1) - 2) ∧
    (dF B E = ell i ∧ dF D F = ell i) ∧
    (dF A D = ell (i + 1) - 1 ∧ dF D G = ell (i + 1) - 1) ∧
    dF A G = ell (i + 2) - 2 := by
  intro s A B C D E F G dF
  exact TSPSP.step i hi (TSPSP.profile i hi)
