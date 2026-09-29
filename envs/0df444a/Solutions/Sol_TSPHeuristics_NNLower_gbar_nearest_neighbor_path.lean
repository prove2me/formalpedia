-- Prove2me | solution 1 for TSPHeuristics.NNLower.gbar_nearest_neighbor_path
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:03:06.916443+00:00
-- url     : https://prove2.me/submissions/da38a3eb-dbba-4882-ba15-3f3fc1a8c427

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

theorem aux_gnn_nn_succ (j : ℕ) : numNodes (j+1) = 2 * numNodes j + 1 := by
  unfold numNodes
  have h1 : 1 ≤ 2 ^ (j+1) := Nat.one_le_two_pow
  rw [pow_succ 2 (j+1)]; omega

theorem aux_gnn_nn_pos (j : ℕ) : 1 ≤ numNodes j := by
  unfold numNodes
  have h1 : 2 ≤ 2 ^ (j+1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem aux_gnn_mid_succ (j : ℕ) : middle (j+1) = numNodes j := rfl

theorem aux_gnn_mid_lt (j : ℕ) : middle j < numNodes j := by
  unfold middle numNodes
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [pow_succ]; omega

theorem aux_gnn_ell_rec1 (j : ℕ) : 2 * ell j - 1 ≤ ell (j+1) ∧ ell (j+1) ≤ 2 * ell j := by
  unfold ell
  rw [pow_succ, pow_succ]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> constructor <;> linarith

theorem aux_gnn_ell_rec2 (j : ℕ) : ell (j+2) = ell (j+1) + 2 * ell j - 1 := by
  unfold ell
  simp only [pow_succ]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> ring

theorem aux_gnn_ell_one : ell 1 = 2 := by norm_num [ell]
theorem aux_gnn_ell_two : ell 2 = 3 := by norm_num [ell]

theorem aux_gnn_ell_ge (j : ℕ) : 2 ≤ ell (j+1) := by
  induction j with
  | zero => rw [aux_gnn_ell_one]
  | succ n ih => have := (aux_gnn_ell_rec1 (n+1)).1; linarith

/-! pathP -/

theorem aux_gnn_P_succ (j : ℕ) : pathP (j+2) =
    pathP (j+1) ++ (pathP (j+1)).map (· + (numNodes (j+1) + 1)) ++ [numNodes (j+1)] := rfl

theorem aux_gnn_P_len (j : ℕ) : (pathP (j+1)).length = numNodes (j+1) := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [aux_gnn_P_succ, aux_gnn_nn_succ (n+1)]
    simp [ih]; ring

theorem aux_gnn_P_lt (j : ℕ) : ∀ x ∈ pathP (j+1), x < numNodes (j+1) := by
  induction j with
  | zero => intro x hx; simp [pathP] at hx; simp [numNodes]; omega
  | succ n ih =>
    intro x hx
    rw [aux_gnn_P_succ] at hx
    rw [aux_gnn_nn_succ (n+1)]
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | rfl
    · have := ih x hx; omega
    · have := ih y hy; omega
    · omega

theorem aux_gnn_P_nodup (j : ℕ) : (pathP (j+1)).Nodup := by
  induction j with
  | zero => simp [pathP]
  | succ n ih =>
    rw [aux_gnn_P_succ]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨ih, ?_, ?_⟩, by simp, ?_⟩
    · exact ih.map (fun a b h => by simpa using h)
    · intro a ha b hb
      simp only [List.mem_map] at hb
      obtain ⟨c, _, rfl⟩ := hb
      have := aux_gnn_P_lt n a ha; omega
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ha | ⟨c, _, rfl⟩
      · have := aux_gnn_P_lt n a ha; omega
      · omega

theorem aux_gnn_P_mem (j : ℕ) : ∀ z < numNodes (j+1), z ∈ pathP (j+1) := by
  induction j with
  | zero => intro z hz; simp [numNodes] at hz; simp [pathP]; omega
  | succ n ih =>
    intro z hz
    rw [aux_gnn_nn_succ (n+1)] at hz
    rw [aux_gnn_P_succ]
    simp only [List.mem_append, List.mem_map, List.mem_singleton]
    by_cases h1 : z < numNodes (n+1)
    · exact Or.inl (Or.inl (ih z h1))
    · by_cases h2 : z = numNodes (n+1)
      · exact Or.inr h2
      · refine Or.inl (Or.inr ⟨z - (numNodes (n+1) + 1), ih _ (by omega), by omega⟩)

theorem aux_gnn_P_get_left (j k : ℕ) (hk : k < numNodes (j+1)) :
    (pathP (j+2)).getD k 0 = (pathP (j+1)).getD k 0 := by
  rw [aux_gnn_P_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [aux_gnn_P_len]; omega),
    List.getElem?_append_left (by simp [aux_gnn_P_len]; omega)]

theorem aux_gnn_P_get_right (j k : ℕ) (hk : k < numNodes (j+1)) :
    (pathP (j+2)).getD (numNodes (j+1) + k) 0 = (pathP (j+1)).getD k 0 + (numNodes (j+1) + 1) := by
  rw [aux_gnn_P_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [aux_gnn_P_len]; omega),
    List.getElem?_append_right (by simp [aux_gnn_P_len])]
  simp only [aux_gnn_P_len, Nat.add_sub_cancel_left, List.getElem?_map]
  have : k < (pathP (j+1)).length := by rw [aux_gnn_P_len]; exact hk
  rw [List.getElem?_eq_getElem this]
  simp

theorem aux_gnn_P_get_last (j : ℕ) :
    (pathP (j+2)).getD (2 * numNodes (j+1)) 0 = numNodes (j+1) := by
  rw [aux_gnn_P_succ]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [aux_gnn_P_len]; omega)]
  simp [aux_gnn_P_len, two_mul]

theorem aux_gnn_P_head (j : ℕ) : (pathP (j+1)).getD 0 0 = 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [aux_gnn_P_get_left n 0 (by have := aux_gnn_nn_pos (n+1); omega), ih]

theorem aux_gnn_P_last (j : ℕ) : (pathP (j+1)).getD (numNodes (j+1) - 1) 0 = middle (j+1) := by
  cases j with
  | zero => rfl
  | succ n =>
    rw [aux_gnn_nn_succ (n+1), show 2 * numNodes (n + 1) + 1 - 1 = 2 * numNodes (n+1) by omega,
      aux_gnn_P_get_last, aux_gnn_mid_succ]


/-! edgesF -/

theorem aux_gnn_F_succ (j : ℕ) : edgesF (j+2) =
    edgesF (j+1) ++
      (edgesF (j+1)).map (fun e => (e.1 + (numNodes (j+1) + 1), e.2.1 + (numNodes (j+1) + 1), e.2.2)) ++
      [(numNodes (j+1) - 1, numNodes (j+1), 1),
       (numNodes (j+1), numNodes (j+1) + 1, 1),
       (numNodes (j+1), numNodes (j+1) + 1 + middle (j+1), ell (j+1)),
       (middle (j+1), numNodes (j+1) + 1, ell (j+1))] := by
  rw [edgesF]

theorem aux_gnn_F_mem (j : ℕ) (a b : ℕ) (w : ℝ) (h : (a, b, w) ∈ edgesF (j+2)) :
    (a, b, w) ∈ edgesF (j+1) ∨
    (∃ a' b', (a', b', w) ∈ edgesF (j+1) ∧ a = a' + (numNodes (j+1) + 1) ∧
      b = b' + (numNodes (j+1) + 1)) ∨
    (a = numNodes (j+1) - 1 ∧ b = numNodes (j+1) ∧ w = 1) ∨
    (a = numNodes (j+1) ∧ b = numNodes (j+1) + 1 ∧ w = 1) ∨
    (a = numNodes (j+1) ∧ b = numNodes (j+1) + 1 + middle (j+1) ∧ w = ell (j+1)) ∨
    (a = middle (j+1) ∧ b = numNodes (j+1) + 1 ∧ w = ell (j+1)) := by
  rw [aux_gnn_F_succ] at h
  simp only [List.mem_append, List.mem_map, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h
  rcases h with (h | ⟨⟨a', b', w'⟩, he, h1, h2, h3⟩) | h
  · exact Or.inl h
  · subst h3; exact Or.inr (Or.inl ⟨a', b', he, h1.symm, h2.symm⟩)
  · right; right; exact h

theorem aux_gnn_F_lt (j : ℕ) : ∀ a b w, (a, b, w) ∈ edgesF (j+1) →
    a < numNodes (j+1) ∧ b < numNodes (j+1) := by
  induction j with
  | zero =>
    intro a b w h
    simp [edgesF] at h
    simp [numNodes]; omega
  | succ n ih =>
    intro a b w h
    have hm := aux_gnn_mid_lt (n+1)
    have hp := aux_gnn_nn_pos (n+1)
    rw [aux_gnn_nn_succ (n+1)]
    rcases aux_gnn_F_mem n a b w h with h | ⟨a', b', hh, rfl, rfl⟩ | h | h | h | h
    · have := ih a b w h; omega
    · have := ih a' b' w hh; omega
    all_goals omega

theorem aux_gnn_F_w (j : ℕ) : ∀ a b w, (a, b, w) ∈ edgesF (j+1) → 1 ≤ w := by
  induction j with
  | zero =>
    intro a b w h
    simp [edgesF] at h
    rcases h with h | h | h <;> linarith [h.2.2]
  | succ n ih =>
    intro a b w h
    have := aux_gnn_ell_ge n
    rcases aux_gnn_F_mem n a b w h with h | ⟨a', b', hh, rfl, rfl⟩ | h | h | h | h
    · exact ih a b w h
    · exact ih a' b' w hh
    · linarith [h.2.2]
    · linarith [h.2.2]
    · rw [h.2.2]; linarith
    · rw [h.2.2]; linarith

theorem aux_gnn_F_cons (j : ℕ) : ∀ a, a + 1 < numNodes (j+1) → (a, a + 1, (1:ℝ)) ∈ edgesF (j+1) := by
  induction j with
  | zero =>
    intro a h
    have h3 : numNodes (0+1) = 3 := rfl
    rw [h3] at h
    have h4 : a < 2 := by omega
    interval_cases a <;> simp [edgesF]
  | succ n ih =>
    intro a h
    rw [aux_gnn_nn_succ (n+1)] at h
    rw [aux_gnn_F_succ]
    simp only [List.mem_append, List.mem_map, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false]
    have hp := aux_gnn_nn_pos (n+1)
    by_cases h1 : a + 1 < numNodes (n+1)
    · exact Or.inl (Or.inl (ih a h1))
    · by_cases h2 : a + 1 = numNodes (n+1)
      · right; left; exact ⟨by omega, by omega, trivial⟩
      · by_cases h3 : a = numNodes (n+1)
        · right; right; left; exact ⟨by omega, by omega, trivial⟩
        · left; right
          refine ⟨(a - (numNodes (n+1) + 1), a - (numNodes (n+1) + 1) + 1, 1), ih _ (by omega), ?_, ?_, rfl⟩ <;>
            simp <;> omega

/-! walks -/

def aux_gnn_Lip (E : List (ℕ × ℕ × ℝ)) (φ : ℕ → ℝ) : Prop :=
  ∀ a b w, (a, b, w) ∈ E → |φ a - φ b| ≤ w

theorem aux_gnn_walk_lip {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ} (hφ : aux_gnn_Lip E φ)
    {x y : ℕ} {c : ℝ} (h : WalkCost E x y c) : |φ x - φ y| ≤ c := by
  induction h with
  | nil x => simp
  | @cons x y z w c he _ ih =>
    have h1 : |φ x - φ y| ≤ w := by
      rcases he with he | he
      · exact hφ _ _ _ he
      · rw [abs_sub_comm]; exact hφ _ _ _ he
    calc |φ x - φ z| = |(φ x - φ y) + (φ y - φ z)| := by ring_nf
      _ ≤ |φ x - φ y| + |φ y - φ z| := abs_add_le _ _
      _ ≤ w + c := add_le_add h1 ih

theorem aux_gnn_walk_ne {E : List (ℕ × ℕ × ℝ)} (hE : ∀ a b w, (a, b, w) ∈ E → 1 ≤ w)
    {x y : ℕ} {c : ℝ} (hxy : x ≠ y) (h : WalkCost E x y c) : 1 ≤ c := by
  have hl : aux_gnn_Lip E (fun z => if z = x then 0 else 1) := by
    intro a b w hab
    have := hE a b w hab
    dsimp only
    split_ifs <;> simp <;> linarith
  have := aux_gnn_walk_lip hl h
  simp [Ne.symm hxy] at this
  exact this

theorem aux_gnn_walk_nonneg {E : List (ℕ × ℕ × ℝ)} (hE : ∀ a b w, (a, b, w) ∈ E → 1 ≤ w)
    {x y : ℕ} {c : ℝ} (h : WalkCost E x y c) : 0 ≤ c := by
  have hl : aux_gnn_Lip E (fun _ => 0) := by
    intro a b w hab
    have := hE a b w hab
    simp; linarith
  have := aux_gnn_walk_lip hl h
  simpa using this

theorem aux_gnn_walk_fwd {E : List (ℕ × ℕ × ℝ)} {n : ℕ}
    (hE : ∀ a, a + 1 < n → (a, a + 1, (1:ℝ)) ∈ E) :
    ∀ d a, a + d < n → ∃ c, WalkCost E a (a + d) c := by
  intro d
  induction d with
  | zero => intro a _; exact ⟨0, WalkCost.nil a⟩
  | succ d ih =>
    intro a h
    obtain ⟨c, hc⟩ := ih (a+1) (by omega)
    refine ⟨1 + c, ?_⟩
    have := WalkCost.cons (Or.inl (hE a (by omega))) hc
    rwa [show a + 1 + d = a + (d + 1) by omega] at this

theorem aux_gnn_walk_bwd {E : List (ℕ × ℕ × ℝ)} {n : ℕ}
    (hE : ∀ a, a + 1 < n → (a, a + 1, (1:ℝ)) ∈ E) :
    ∀ d a, a + d < n → ∃ c, WalkCost E (a + d) a c := by
  intro d
  induction d with
  | zero => intro a _; exact ⟨0, WalkCost.nil a⟩
  | succ d ih =>
    intro a h
    obtain ⟨c, hc⟩ := ih a (by omega)
    refine ⟨1 + c, ?_⟩
    have h1 : (a + d, a + (d + 1), (1:ℝ)) ∈ E := hE (a + d) (by omega)
    exact WalkCost.cons (Or.inr h1) hc

theorem aux_gnn_conn {E : List (ℕ × ℕ × ℝ)} {n : ℕ}
    (hE : ∀ a, a + 1 < n → (a, a + 1, (1:ℝ)) ∈ E) (x y : ℕ) (hx : x < n) (hy : y < n) :
    ∃ c, WalkCost E x y c := by
  rcases le_total x y with h | h
  · obtain ⟨c, hc⟩ := aux_gnn_walk_fwd hE (y - x) x (by omega)
    rw [show x + (y - x) = y by omega] at hc
    exact ⟨c, hc⟩
  · obtain ⟨c, hc⟩ := aux_gnn_walk_bwd hE (x - y) y (by omega)
    rw [show y + (x - y) = x by omega] at hc
    exact ⟨c, hc⟩


/-! potentials -/

theorem aux_gnn_min2 (K u v w : ℝ) (h : |u - v| ≤ w) : |min K u - min K v| ≤ w := by
  have := abs_min_sub_min_le_max K u K v
  simp only [sub_self, abs_zero] at this
  exact this.trans (max_le (le_trans (abs_nonneg _) h) h)

theorem aux_gnn_min3 (K p q u1 u2 v1 v2 w : ℝ) (h1 : |u1 - v1| ≤ w) (h2 : |u2 - v2| ≤ w) :
    |min K (min (p + u1) (q + u2)) - min K (min (p + v1) (q + v2))| ≤ w := by
  apply aux_gnn_min2
  have := abs_min_sub_min_le_max (p + u1) (q + u2) (p + v1) (q + v2)
  rw [show p + u1 - (p + v1) = u1 - v1 by ring, show q + u2 - (q + v2) = u2 - v2 by ring] at this
  exact this.trans (max_le h1 h2)

theorem aux_gnn_pot (j : ℕ) : ∃ Φ Ψ : ℕ → ℝ, aux_gnn_Lip (edgesF (j+1)) Φ ∧
    aux_gnn_Lip (edgesF (j+1)) Ψ ∧ (∀ x, 0 ≤ Φ x) ∧ (∀ x, 0 ≤ Ψ x) ∧
    Φ (middle (j+1)) = 0 ∧ ell (j+1) - 1 ≤ Φ 0 ∧ ell (j+1) - 1 ≤ Φ (numNodes (j+1) - 1) ∧
    Ψ 0 = 0 ∧ ell (j+2) - 2 ≤ Ψ (numNodes (j+1) - 1) ∧ ell (j+1) - 1 ≤ Ψ (middle (j+1)) := by
  induction j with
  | zero =>
    refine ⟨fun x => if x = 1 then 0 else 1, fun x => if x = 0 then 0 else 1, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b w h
      simp [edgesF] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
    · intro a b w h
      simp [edgesF] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
    · intro x; dsimp only; split_ifs <;> norm_num
    · intro x; dsimp only; split_ifs <;> norm_num
    · rfl
    · simp [aux_gnn_ell_one]; norm_num
    · simp [aux_gnn_ell_one, numNodes]; norm_num
    · simp
    · simp [aux_gnn_ell_two, numNodes]; norm_num
    · simp [aux_gnn_ell_one, middle]; norm_num
  | succ n ih =>
    obtain ⟨Φ, Ψ, hLΦ, hLΨ, hΦ0, hΨ0, hΦm, hΦs, hΦr, hΨs, hΨr, hΨm⟩ := ih
    have hl2 := aux_gnn_ell_ge n
    have hr1 := aux_gnn_ell_rec1 (n+1)
    have hr2 := aux_gnn_ell_rec2 (n+1)
    have hsp := aux_gnn_nn_pos (n+1)
    have hml := aux_gnn_mid_lt (n+1)
    -- abbreviations as hypotheses
    obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, R = fun x => max 0 (ell (n+2) - 2 - Ψ x) := ⟨_, rfl⟩
    have hR0 : ∀ x, 0 ≤ R x := fun x => by rw [hR]; exact le_max_left _ _
    have hRL : aux_gnn_Lip (edgesF (n+1)) R := by
      intro a b w h
      rw [hR]
      have := abs_max_sub_max_le_max 0 (ell (n+2) - 2 - Ψ a) 0 (ell (n+2) - 2 - Ψ b)
      rw [show ell (n+2) - 2 - Ψ a - (ell (n+2) - 2 - Ψ b) = -(Ψ a - Ψ b) by ring, abs_neg,
        sub_self, abs_zero] at this
      exact this.trans (max_le ((abs_nonneg _).trans (hLΨ a b w h)) (hLΨ a b w h))
    have hRr : R (numNodes (n+1) - 1) = 0 := by
      rw [hR]; simp only; rw [max_eq_left]; linarith
    have hRs : ell (n+2) - 2 ≤ R 0 := by
      rw [hR]; simp only; rw [hΨs]; exact le_max_of_le_right (by linarith)
    obtain ⟨Φ', hΦ'⟩ : ∃ f : ℕ → ℝ, f = fun x =>
        if x < numNodes (n+1) then
          min (ell (n+2) - 1) (min (1 + R x) (1 + ell (n+1) + Φ x))
        else if x = numNodes (n+1) then 0
        else min (ell (n+2) - 1) (min (1 + Ψ (x - (numNodes (n+1) + 1)))
          (ell (n+1) + Φ (x - (numNodes (n+1) + 1)))) := ⟨_, rfl⟩
    obtain ⟨Ψ', hΨ'⟩ : ∃ f : ℕ → ℝ, f = fun x =>
        if x < numNodes (n+1) then min (ell (n+2)) (Ψ x)
        else if x = numNodes (n+1) then ell (n+2) - 1
        else min (ell (n+3) - 2) (min (2 * ell (n+1) - 1 + Ψ (x - (numNodes (n+1) + 1)))
          (ell (n+2) - 1 + ell (n+1) + Φ (x - (numNodes (n+1) + 1)))) := ⟨_, rfl⟩
    have eΦL : ∀ x, x < numNodes (n+1) → Φ' x =
        min (ell (n+2) - 1) (min (1 + R x) (1 + ell (n+1) + Φ x)) := by
      intro x hx; rw [hΦ']; simp [hx]
    have eΦD : Φ' (numNodes (n+1)) = 0 := by rw [hΦ']; simp
    have eΦR : ∀ x, Φ' (x + (numNodes (n+1) + 1)) =
        min (ell (n+2) - 1) (min (1 + Ψ x) (ell (n+1) + Φ x)) := by
      intro x; rw [hΦ']; simp only
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    have eΨL : ∀ x, x < numNodes (n+1) → Ψ' x = min (ell (n+2)) (Ψ x) := by
      intro x hx; rw [hΨ']; simp [hx]
    have eΨD : Ψ' (numNodes (n+1)) = ell (n+2) - 1 := by rw [hΨ']; simp
    have eΨR : ∀ x, Ψ' (x + (numNodes (n+1) + 1)) =
        min (ell (n+3) - 2) (min (2 * ell (n+1) - 1 + Ψ x) (ell (n+2) - 1 + ell (n+1) + Φ x)) := by
      intro x; rw [hΨ']; simp only
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    have hΦ'0 : ∀ x, 0 ≤ Φ' x := by
      intro x
      rw [hΦ']; simp only
      split_ifs
      · exact le_min (by linarith) (le_min (by linarith [hR0 x]) (by linarith [hΦ0 x]))
      · exact le_refl _
      · exact le_min (by linarith) (le_min (by linarith [hΨ0 (x - (numNodes (n+1) + 1))])
          (by linarith [hΦ0 (x - (numNodes (n+1) + 1))]))
    have hΨ'0 : ∀ x, 0 ≤ Ψ' x := by
      intro x
      rw [hΨ']; simp only
      split_ifs
      · exact le_min (by linarith) (hΨ0 x)
      · linarith
      · exact le_min (by linarith) (le_min (by linarith [hΨ0 (x - (numNodes (n+1) + 1))])
          (by linarith [hΦ0 (x - (numNodes (n+1) + 1))]))
    -- values at the ports of the copies
    have vΦE : Φ' (0 + (numNodes (n+1) + 1)) = 1 := by
      rw [eΦR, hΨs]
      apply le_antisymm
      · exact min_le_of_right_le (min_le_of_left_le (by linarith))
      · exact le_min (by linarith) (le_min (by linarith) (by linarith [hΦ0 0]))
    have vΨE : Ψ' (0 + (numNodes (n+1) + 1)) = 2 * ell (n+1) - 1 := by
      rw [eΨR, hΨs]
      apply le_antisymm
      · exact min_le_of_right_le (min_le_of_left_le (by linarith))
      · exact le_min (by linarith) (le_min (by linarith) (by linarith [hΦ0 0]))
    have hmid : middle (n+2) = numNodes (n+1) := aux_gnn_mid_succ (n+1)
    have hnn : numNodes (n+2) - 1 = (numNodes (n+1) - 1) + (numNodes (n+1) + 1) := by
      rw [aux_gnn_nn_succ (n+1)]; omega
    refine ⟨Φ', Ψ', ?_, ?_, hΦ'0, hΨ'0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b w h
      rcases aux_gnn_F_mem n a b w h with h | ⟨a', b', hh, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨ha, hb⟩ := aux_gnn_F_lt n a b w h
        rw [eΦL a ha, eΦL b hb]
        exact aux_gnn_min3 _ _ _ _ _ _ _ _ (hRL a b w h) (hLΦ a b w h)
      · rw [eΦR, eΦR]
        exact aux_gnn_min3 _ _ _ _ _ _ _ _ (hLΨ a' b' w hh) (hLΦ a' b' w hh)
      · rw [eΦL _ (by omega), eΦD, hRr, sub_zero, abs_le]
        have := hΦ'0 (numNodes (n+1) - 1)
        rw [eΦL _ (by omega), hRr] at this
        constructor
        · linarith
        · exact min_le_of_right_le (min_le_of_left_le (by linarith))
      · rw [eΦD, show numNodes (n+1) + 1 = 0 + (numNodes (n+1) + 1) by ring, vΦE]; norm_num
      · rw [eΦD, show numNodes (n+1) + 1 + middle (n+1) = middle (n+1) + (numNodes (n+1) + 1) by ring]
        have := hΦ'0 (middle (n+1) + (numNodes (n+1) + 1))
        rw [eΦR, hΦm] at *
        rw [zero_sub, abs_neg, abs_le]
        constructor
        · linarith
        · exact min_le_of_right_le (min_le_of_right_le (by linarith))
      · rw [show numNodes (n+1) + 1 = 0 + (numNodes (n+1) + 1) by ring, vΦE]
        have := hΦ'0 (middle (n+1))
        rw [eΦL _ hml, hΦm] at *
        rw [abs_le]
        constructor
        · linarith
        · have : min (ell (n+2) - 1) (min (1 + R (middle (n+1))) (1 + ell (n+1) + 0)) ≤
            1 + ell (n+1) + 0 := min_le_of_right_le (min_le_right _ _)
          linarith
    · intro a b w h
      rcases aux_gnn_F_mem n a b w h with h | ⟨a', b', hh, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨ha, hb⟩ := aux_gnn_F_lt n a b w h
        rw [eΨL a ha, eΨL b hb]
        exact aux_gnn_min2 _ _ _ _ (hLΨ a b w h)
      · rw [eΨR, eΨR]
        exact aux_gnn_min3 _ _ _ _ _ _ _ _ (hLΨ a' b' w hh) (hLΦ a' b' w hh)
      · rw [eΨL _ (by omega), eΨD, abs_le]
        have h1 : ell (n+2) - 2 ≤ min (ell (n+2)) (Ψ (numNodes (n+1) - 1)) :=
          le_min (by linarith) hΨr
        have h2 : min (ell (n+2)) (Ψ (numNodes (n+1) - 1)) ≤ ell (n+2) := min_le_left _ _
        constructor <;> linarith
      · rw [eΨD, show numNodes (n+1) + 1 = 0 + (numNodes (n+1) + 1) by ring, vΨE, abs_le]
        constructor <;> linarith
      · rw [eΨD, show numNodes (n+1) + 1 + middle (n+1) = middle (n+1) + (numNodes (n+1) + 1) by ring,
          eΨR, hΦm, abs_le]
        have h1 : min (ell (n+3) - 2) (min (2 * ell (n+1) - 1 + Ψ (middle (n+1)))
            (ell (n+2) - 1 + ell (n+1) + 0)) ≤ ell (n+2) - 1 + ell (n+1) + 0 :=
          min_le_of_right_le (min_le_right _ _)
        have h2 : ell (n+2) - 1 - ell (n+1) ≤ min (ell (n+3) - 2) (min (2 * ell (n+1) - 1 +
            Ψ (middle (n+1))) (ell (n+2) - 1 + ell (n+1) + 0)) :=
          le_min (by linarith) (le_min (by linarith) (by linarith))
        constructor <;> linarith
      · rw [show numNodes (n+1) + 1 = 0 + (numNodes (n+1) + 1) by ring, vΨE, eΨL _ hml, abs_le]
        have h1 : ell (n+1) - 1 ≤ min (ell (n+2)) (Ψ (middle (n+1))) :=
          le_min (by linarith) hΨm
        have h2 : min (ell (n+2)) (Ψ (middle (n+1))) ≤ ell (n+2) := min_le_left _ _
        constructor <;> linarith
    · rw [hmid, eΦD]
    · rw [eΦL 0 (by omega)]
      exact le_min (le_refl _) (le_min (by linarith) (by linarith))
    · rw [hnn, eΦR]
      exact le_min (le_refl _) (le_min (by linarith) (by linarith))
    · rw [eΨL 0 (by omega), hΨs]; exact min_eq_right (by linarith)
    · rw [hnn, eΨR]
      exact le_min (le_refl _) (le_min (by linarith) (by linarith))
    · rw [hmid, eΨD]


/-! isolation of a copy and the key lower bound -/

def aux_gnn_Good (E : List (ℕ × ℕ × ℝ)) (j o : ℕ) (μ : ℝ) : Prop :=
  (∀ a b w, (a, b, w) ∈ E → 1 ≤ w) ∧
  (∀ a b w, (a, b, w) ∈ edgesF j → (a + o, b + o, w) ∈ E) ∧
  (∀ a b w, (a, b, w) ∈ E → (∀ a' b', (a', b', w) ∈ edgesF j → ¬(a = a' + o ∧ b = b' + o)) →
    ∀ x, (x = a ∨ x = b) → o ≤ x → x < o + numNodes j →
      x = o ∨ x = o + numNodes j - 1 ∨ (x = o + middle j ∧ μ ≤ w))

theorem aux_gnn_good_mono {E : List (ℕ × ℕ × ℝ)} {j o : ℕ} {μ μ' : ℝ}
    (hG : aux_gnn_Good E j o μ) (h : μ' ≤ μ) : aux_gnn_Good E j o μ' := by
  refine ⟨hG.1, hG.2.1, ?_⟩
  intro a b w hab hn x hx h1 h2
  rcases hG.2.2 a b w hab hn x hx h1 h2 with h3 | h3 | ⟨h3, h4⟩
  · exact Or.inl h3
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr ⟨h3, le_trans h h4⟩)

theorem aux_gnn_key (j : ℕ) (E : List (ℕ × ℕ × ℝ)) (o : ℕ)
    (hG : aux_gnn_Good E (j+1) o (ell (j+1))) (y : ℕ)
    (hy : ¬ (o ≤ y ∧ y < o + numNodes (j+1))) (c : ℝ)
    (hw : WalkCost E (o + middle (j+1)) y c) : ell (j+1) ≤ c := by
  obtain ⟨Φ, -, hLΦ, -, hΦ0, -, hΦm, hΦs, hΦr, -⟩ := aux_gnn_pot j
  have hl2 := aux_gnn_ell_ge j
  have hsp := aux_gnn_nn_pos (j+1)
  have hml := aux_gnn_mid_lt (j+1)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, φ = fun x =>
      if o ≤ x ∧ x < o + numNodes (j+1) then min (ell (j+1)) (Φ (x - o)) else ell (j+1) :=
    ⟨_, rfl⟩
  have hin : ∀ x, x < numNodes (j+1) → φ (x + o) = min (ell (j+1)) (Φ x) := by
    intro x hx; rw [hφ]; simp only
    rw [if_pos (by omega), Nat.add_sub_cancel]
  have hout : ∀ x, ¬ (o ≤ x ∧ x < o + numNodes (j+1)) → φ x = ell (j+1) := by
    intro x hx; rw [hφ]; simp only; rw [if_neg hx]
  have hbd : ∀ x, 0 ≤ φ x ∧ φ x ≤ ell (j+1) := by
    intro x; rw [hφ]; simp only
    split_ifs
    · exact ⟨le_min (by linarith) (hΦ0 _), min_le_left _ _⟩
    · exact ⟨by linarith, le_refl _⟩
  have hLip : aux_gnn_Lip E φ := by
    intro a b w hab
    by_cases hsh : ∃ a' b', (a', b', w) ∈ edgesF (j+1) ∧ a = a' + o ∧ b = b' + o
    · obtain ⟨a', b', h', rfl, rfl⟩ := hsh
      obtain ⟨ha, hb⟩ := aux_gnn_F_lt j a' b' w h'
      rw [hin a' ha, hin b' hb]
      exact aux_gnn_min2 _ _ _ _ (hLΦ a' b' w h')
    · push Not at hsh
      have hn : ∀ a' b', (a', b', w) ∈ edgesF (j+1) → ¬(a = a' + o ∧ b = b' + o) := by
        intro a' b' h' ⟨h1, h2⟩; exact hsh a' b' h' h1 h2
      have hw1 := hG.1 a b w hab
      have cls : ∀ x, (x = a ∨ x = b) → (ell (j+1) - 1 ≤ φ x ∨ ell (j+1) ≤ w) := by
        intro x hx
        by_cases hq : o ≤ x ∧ x < o + numNodes (j+1)
        · rcases hG.2.2 a b w hab hn x hx hq.1 hq.2 with h3 | h3 | ⟨_, h4⟩
          · left; rw [show x = 0 + o by omega, hin 0 (by omega)]
            exact le_min (by linarith) hΦs
          · left; rw [show x = (numNodes (j+1) - 1) + o by omega, hin _ (by omega)]
            exact le_min (by linarith) hΦr
          · right; exact h4
        · left; rw [hout x hq]; linarith
      have ba := hbd a
      have bb := hbd b
      rw [abs_le]
      rcases cls a (Or.inl rfl) with h1 | h1
      · rcases cls b (Or.inr rfl) with h2 | h2
        · constructor <;> linarith
        · constructor <;> linarith
      · constructor <;> linarith
  have := aux_gnn_walk_lip hLip hw
  rw [show o + middle (j+1) = middle (j+1) + o by ring, hin _ hml, hΦm, hout y hy,
    min_eq_right (by linarith), zero_sub, abs_neg, abs_of_nonneg (by linarith)] at this
  exact this

theorem aux_gnn_goodL (n : ℕ) (E : List (ℕ × ℕ × ℝ)) (o : ℕ) (μ : ℝ)
    (hG : aux_gnn_Good E (n+2) o μ) : aux_gnn_Good E (n+1) o (ell (n+1)) := by
  have hsp := aux_gnn_nn_pos (n+1)
  have hml := aux_gnn_mid_lt (n+1)
  have hns : numNodes (n+2) = 2 * numNodes (n+1) + 1 := aux_gnn_nn_succ (n+1)
  have hmid : middle (n+2) = numNodes (n+1) := aux_gnn_mid_succ (n+1)
  refine ⟨hG.1, ?_, ?_⟩
  · intro a b w h
    apply hG.2.1
    rw [aux_gnn_F_succ]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
  · intro a b w hab hnot x hx hox hxn
    by_cases hin : ∃ a' b', (a', b', w) ∈ edgesF (n+2) ∧ a = a' + o ∧ b = b' + o
    · obtain ⟨a', b', h', rfl, rfl⟩ := hin
      rcases aux_gnn_F_mem n a' b' w h' with h'' | ⟨a'', b'', _, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact absurd ⟨rfl, rfl⟩ (hnot a' b' h'')
      · exfalso; omega
      · right; left; omega
      · exfalso; omega
      · exfalso; omega
      · rcases hx with rfl | rfl
        · right; right; exact ⟨by omega, le_refl _⟩
        · exfalso; omega
    · push Not at hin
      have hn2 : ∀ a' b', (a', b', w) ∈ edgesF (n+2) → ¬(a = a' + o ∧ b = b' + o) := by
        intro a' b' h' ⟨h1, h2⟩; exact hin a' b' h' h1 h2
      rcases hG.2.2 a b w hab hn2 x hx hox (by omega) with h3 | h3 | ⟨h3, _⟩
      · exact Or.inl h3
      · exfalso; omega
      · exfalso; omega

theorem aux_gnn_goodR (n : ℕ) (E : List (ℕ × ℕ × ℝ)) (o : ℕ) (μ : ℝ)
    (hG : aux_gnn_Good E (n+2) o μ) :
    aux_gnn_Good E (n+1) (o + numNodes (n+1) + 1) (ell (n+1)) := by
  have hsp := aux_gnn_nn_pos (n+1)
  have hml := aux_gnn_mid_lt (n+1)
  have hns : numNodes (n+2) = 2 * numNodes (n+1) + 1 := aux_gnn_nn_succ (n+1)
  have hmid : middle (n+2) = numNodes (n+1) := aux_gnn_mid_succ (n+1)
  refine ⟨hG.1, ?_, ?_⟩
  · intro a b w h
    have hm : (a + (numNodes (n+1) + 1), b + (numNodes (n+1) + 1), w) ∈ edgesF (n+2) := by
      rw [aux_gnn_F_succ]
      refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
      exact List.mem_map.mpr ⟨(a, b, w), h, rfl⟩
    have := hG.2.1 _ _ _ hm
    rwa [show a + (numNodes (n+1) + 1) + o = a + (o + numNodes (n+1) + 1) by ring,
      show b + (numNodes (n+1) + 1) + o = b + (o + numNodes (n+1) + 1) by ring] at this
  · intro a b w hab hnot x hx hox hxn
    by_cases hin : ∃ a' b', (a', b', w) ∈ edgesF (n+2) ∧ a = a' + o ∧ b = b' + o
    · obtain ⟨a', b', h', rfl, rfl⟩ := hin
      rcases aux_gnn_F_mem n a' b' w h' with h'' | ⟨a'', b'', h3, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨h4, h5⟩ := aux_gnn_F_lt n a' b' w h''
        exfalso; omega
      · exact absurd ⟨by ring, by ring⟩ (hnot a'' b'' h3)
      · exfalso; omega
      · rcases hx with rfl | rfl
        · exfalso; omega
        · left; omega
      · rcases hx with rfl | rfl
        · exfalso; omega
        · right; right; exact ⟨by omega, le_refl _⟩
      · rcases hx with rfl | rfl
        · exfalso; omega
        · left; omega
    · push Not at hin
      have hn2 : ∀ a' b', (a', b', w) ∈ edgesF (n+2) → ¬(a = a' + o ∧ b = b' + o) := by
        intro a' b' h' ⟨h1, h2⟩; exact hin a' b' h' h1 h2
      rcases hG.2.2 a b w hab hn2 x hx (by omega) (by omega) with h3 | h3 | ⟨h3, _⟩
      · exfalso; omega
      · right; left; omega
      · exfalso; omega


/-! the nearest-neighbor steps -/

theorem aux_gnn_P_idx (j z : ℕ) (hz : z < numNodes (j+1)) :
    ∃ i < numNodes (j+1), (pathP (j+1)).getD i 0 = z := by
  have hm := aux_gnn_P_mem j z hz
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by rw [← aux_gnn_P_len]; exact hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, he]

theorem aux_gnn_main (j : ℕ) : ∀ (E : List (ℕ × ℕ × ℝ)) (o : ℕ), aux_gnn_Good E (j+1) o 1 →
    ∀ k, k + 1 < numNodes (j+1) →
    ∃ w, ((o + (pathP (j+1)).getD k 0, o + (pathP (j+1)).getD (k+1) 0, w) ∈ E ∨
        (o + (pathP (j+1)).getD (k+1) 0, o + (pathP (j+1)).getD k 0, w) ∈ E) ∧
      ∀ y, (∀ i ≤ k, y ≠ o + (pathP (j+1)).getD i 0) →
        ∀ c, WalkCost E (o + (pathP (j+1)).getD k 0) y c → w ≤ c := by
  induction j with
  | zero =>
    intro E o hG k hk
    have h3 : numNodes (0+1) = 3 := rfl
    rw [h3] at hk
    have hk2 : k < 2 := by omega
    interval_cases k
    · refine ⟨1, Or.inl ?_, ?_⟩
      · have := hG.2.1 0 2 1 (by simp [edgesF])
        simpa [pathP, add_comm] using this
      · intro y hy c hc
        exact aux_gnn_walk_ne hG.1 (fun h => hy 0 (le_refl _) h.symm) hc
    · refine ⟨1, Or.inr ?_, ?_⟩
      · have := hG.2.1 1 2 1 (by simp [edgesF])
        simpa [pathP, add_comm] using this
      · intro y hy c hc
        exact aux_gnn_walk_ne hG.1 (fun h => hy 1 (le_refl _) h.symm) hc
  | succ n ih =>
    intro E o hG k hk
    have hsp := aux_gnn_nn_pos (n+1)
    have hml := aux_gnn_mid_lt (n+1)
    have hns : numNodes (n+2) = 2 * numNodes (n+1) + 1 := aux_gnn_nn_succ (n+1)
    have hGL := aux_gnn_goodL n E o 1 hG
    have hGR := aux_gnn_goodR n E o 1 hG
    have hl2 := aux_gnn_ell_ge n
    rw [hns] at hk
    by_cases c1 : k + 1 < numNodes (n+1)
    · -- inside the left copy
      obtain ⟨w, hedge, hlow⟩ := ih E o (aux_gnn_good_mono hGL (by linarith)) k c1
      refine ⟨w, ?_, ?_⟩
      · rw [aux_gnn_P_get_left n k (by omega), aux_gnn_P_get_left n (k+1) c1]; exact hedge
      · intro y hy c hc
        rw [aux_gnn_P_get_left n k (by omega)] at hc
        refine hlow y (fun i hi => ?_) c hc
        have := hy i hi
        rwa [aux_gnn_P_get_left n i (by omega)] at this
    by_cases c2 : k + 1 = numNodes (n+1)
    · -- the edge (B, E)
      have e1 : (pathP (n+2)).getD k 0 = middle (n+1) := by
        rw [aux_gnn_P_get_left n k (by omega), show k = numNodes (n+1) - 1 by omega, aux_gnn_P_last]
      have e2 : (pathP (n+2)).getD (k+1) 0 = numNodes (n+1) + 1 := by
        rw [c2, show numNodes (n+1) = numNodes (n+1) + 0 by rfl, aux_gnn_P_get_right n 0 hsp,
          aux_gnn_P_head]; ring
      refine ⟨ell (n+1), Or.inl ?_, ?_⟩
      · rw [e1, e2]
        have hm : (middle (n+1), numNodes (n+1) + 1, ell (n+1)) ∈ edgesF (n+2) := by
          rw [aux_gnn_F_succ]; simp
        have := hG.2.1 _ _ _ hm
        rwa [add_comm (middle (n+1)) o, add_comm (numNodes (n+1) + 1) o] at this
      · intro y hy c hc
        rw [e1] at hc
        refine aux_gnn_key n E o hGL y ?_ c hc
        rintro ⟨h1, h2⟩
        obtain ⟨i, hi, he⟩ := aux_gnn_P_idx n (y - o) (by omega)
        have := hy i (by omega)
        rw [aux_gnn_P_get_left n i hi, he] at this
        omega
    by_cases c3 : k + 1 < 2 * numNodes (n+1)
    · -- inside the right copy
      obtain ⟨k', rfl⟩ : ∃ k', k = numNodes (n+1) + k' := ⟨k - numNodes (n+1), by omega⟩
      obtain ⟨w, hedge, hlow⟩ := ih E (o + numNodes (n+1) + 1) (aux_gnn_good_mono hGR (by linarith))
        k' (by omega)
      have e1 := aux_gnn_P_get_right n k' (by omega)
      have e2 := aux_gnn_P_get_right n (k'+1) (by omega)
      rw [show numNodes (n+1) + (k' + 1) = numNodes (n+1) + k' + 1 by ring] at e2
      refine ⟨w, ?_, ?_⟩
      · rw [e1, e2]
        rw [show o + ((pathP (n+1)).getD k' 0 + (numNodes (n+1) + 1)) =
            o + numNodes (n+1) + 1 + (pathP (n+1)).getD k' 0 by ring,
          show o + ((pathP (n+1)).getD (k'+1) 0 + (numNodes (n+1) + 1)) =
            o + numNodes (n+1) + 1 + (pathP (n+1)).getD (k'+1) 0 by ring]
        exact hedge
      · intro y hy c hc
        rw [e1, show o + ((pathP (n+1)).getD k' 0 + (numNodes (n+1) + 1)) =
            o + numNodes (n+1) + 1 + (pathP (n+1)).getD k' 0 by ring] at hc
        refine hlow y (fun i hi => ?_) c hc
        have := hy (numNodes (n+1) + i) (by omega)
        rw [aux_gnn_P_get_right n i (by omega)] at this
        rw [show o + numNodes (n+1) + 1 + (pathP (n+1)).getD i 0 =
          o + ((pathP (n+1)).getD i 0 + (numNodes (n+1) + 1)) by ring]
        exact this
    · -- the edge (F, D)
      have hk' : k = numNodes (n+1) + (numNodes (n+1) - 1) := by omega
      have e1 : (pathP (n+2)).getD k 0 = middle (n+1) + (numNodes (n+1) + 1) := by
        rw [hk', aux_gnn_P_get_right n _ (by omega), aux_gnn_P_last]
      have e2 : (pathP (n+2)).getD (k+1) 0 = numNodes (n+1) := by
        rw [show k + 1 = 2 * numNodes (n+1) by omega, aux_gnn_P_get_last]
      refine ⟨ell (n+1), Or.inr ?_, ?_⟩
      · rw [e1, e2]
        have hm : (numNodes (n+1), numNodes (n+1) + 1 + middle (n+1), ell (n+1)) ∈ edgesF (n+2) := by
          rw [aux_gnn_F_succ]; simp
        have := hG.2.1 _ _ _ hm
        rwa [add_comm (numNodes (n+1)) o,
          show numNodes (n+1) + 1 + middle (n+1) + o = o + (middle (n+1) + (numNodes (n+1) + 1)) by
            ring] at this
      · intro y hy c hc
        rw [e1, show o + (middle (n+1) + (numNodes (n+1) + 1)) =
          o + numNodes (n+1) + 1 + middle (n+1) by ring] at hc
        refine aux_gnn_key n E (o + numNodes (n+1) + 1) hGR y ?_ c hc
        rintro ⟨h1, h2⟩
        obtain ⟨i, hi, he⟩ := aux_gnn_P_idx n (y - (o + numNodes (n+1) + 1)) (by omega)
        have := hy (numNodes (n+1) + i) (by omega)
        rw [aux_gnn_P_get_right n i hi, he] at this
        omega

/-! the top level -/

theorem aux_gnn_topGood (j : ℕ) : aux_gnn_Good (edgesG (j+1)) (j+1) 0 1 := by
  have hl2 := aux_gnn_ell_ge j
  refine ⟨?_, ?_, ?_⟩
  · intro a b w h
    unfold edgesG at h
    simp only [List.mem_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact aux_gnn_F_w j a b w h
    · linarith [h.2.2]
    · rw [h.2.2]; linarith
  · intro a b w h
    unfold edgesG
    simp only [add_zero]
    exact List.mem_append.mpr (Or.inl h)
  · intro a b w h hnot x hx h1 h2
    unfold edgesG at h
    simp only [List.mem_append, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd ⟨by simp, by simp⟩ (hnot a b h)
    · rcases hx with rfl | rfl
      · left; rfl
      · right; left; omega
    · rcases hx with rfl | rfl
      · right; right; exact ⟨by omega, by linarith⟩
      · left; rfl

theorem aux_gnn_finRotate (n : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    ((finRotate n k : Fin n) : ℕ) = k.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coe_finRotate_of_ne_last]
  intro h; rw [h] at hk; simp at hk

end TSPHeuristics.NNLower

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 1 ≤ i) :
    ∃ τ : Equiv.Perm (Fin (numNodes i)),
      (∀ k : Fin (numNodes i), (τ k : ℕ) = (pathP i).getD k 0) ∧
      IsNearestNeighborTour (gbar i) τ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hlen := aux_gnn_P_len j
  have hbound : ∀ k : Fin (numNodes (j+1)), (pathP (j+1)).getD k 0 < numNodes (j+1) := by
    intro k
    have hk : (k : ℕ) < (pathP (j+1)).length := by rw [hlen]; exact k.2
    rw [List.getD_eq_getElem _ _ hk]
    exact aux_gnn_P_lt j _ (List.getElem_mem hk)
  let f : Fin (numNodes (j+1)) → Fin (numNodes (j+1)) :=
    fun k => ⟨(pathP (j+1)).getD k 0, hbound k⟩
  have hinj : Function.Injective f := by
    intro k1 k2 h
    have h' : (pathP (j+1)).getD k1 0 = (pathP (j+1)).getD k2 0 := congrArg Fin.val h
    have hk1 : (k1 : ℕ) < (pathP (j+1)).length := by rw [hlen]; exact k1.2
    have hk2 : (k2 : ℕ) < (pathP (j+1)).length := by rw [hlen]; exact k2.2
    rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at h'
    exact Fin.ext ((List.Nodup.getElem_inj_iff (aux_gnn_P_nodup j)).mp h')
  let τ : Equiv.Perm (Fin (numNodes (j+1))) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ k, (τ k : ℕ) = (pathP (j+1)).getD k 0 := fun k => rfl
  refine ⟨τ, hτ, ?_⟩
  intro k y hk hvis
  have hG := aux_gnn_topGood j
  obtain ⟨w, hedge, hlow⟩ := aux_gnn_main j (edgesG (j+1)) 0 hG k.val hk
  simp only [zero_add] at hedge hlow
  unfold gbar
  rw [hτ, hτ, aux_gnn_finRotate _ k hk]
  have hE1 := hG.1
  have hcons : ∀ a, a + 1 < numNodes (j+1) → (a, a + 1, (1:ℝ)) ∈ edgesG (j+1) := by
    intro a ha
    unfold edgesG
    exact List.mem_append.mpr (Or.inl (aux_gnn_F_cons j a ha))
  have hup : spDist (edgesG (j+1)) ((pathP (j+1)).getD k 0) ((pathP (j+1)).getD (k+1) 0) ≤ w := by
    apply csInf_le ⟨0, fun c hc => aux_gnn_walk_nonneg hE1 hc⟩
    show WalkCost (edgesG (j+1)) ((pathP (j+1)).getD k 0) ((pathP (j+1)).getD (k+1) 0) w
    have := WalkCost.cons hedge (WalkCost.nil ((pathP (j+1)).getD (k+1) 0))
    rwa [add_zero] at this
  have hlo : w ≤ spDist (edgesG (j+1)) ((pathP (j+1)).getD k 0) y := by
    apply le_csInf
    · obtain ⟨c, hc⟩ := aux_gnn_conn hcons _ _ (hbound k) y.2
      exact ⟨c, hc⟩
    · intro c hc
      refine hlow y (fun i hi => ?_) c hc
      intro hyi
      have hin : i < numNodes (j+1) := by omega
      apply hvis ⟨i, hin⟩ (Fin.le_iff_val_le_val.mpr hi)
      apply Fin.ext
      rw [hτ]; exact hyi.symm
  exact hup.trans hlo
