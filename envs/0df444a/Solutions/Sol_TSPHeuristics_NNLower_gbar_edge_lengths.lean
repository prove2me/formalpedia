-- Prove2me | solution 1 for TSPHeuristics.NNLower.gbar_edge_lengths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:37:01.48999+00:00
-- url     : https://prove2.me/submissions/3d16d176-cf5b-4e35-9a22-e4cf0eb106d6

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- `φ` is 1-Lipschitz along every edge of `E`. -/
def aux_gb_Lip (E : List (ℕ × ℕ × ℝ)) (φ : ℕ → ℝ) : Prop :=
  ∀ e ∈ E, |φ e.1 - φ e.2.1| ≤ e.2.2

/-- Gluing a function on the left copy, a value at the new node, and a function on the
right copy. -/
noncomputable def aux_gb_glue (s : ℕ) (f : ℕ → ℝ) (d : ℝ) (g : ℕ → ℝ) (v : ℕ) : ℝ :=
  if v < s then f v else if v = s then d else g (v - (s + 1))

lemma aux_gb_glue_lt {s v : ℕ} {f g : ℕ → ℝ} {d : ℝ} (h : v < s) :
    aux_gb_glue s f d g v = f v := by
  simp [aux_gb_glue, h]

lemma aux_gb_glue_self {s : ℕ} {f g : ℕ → ℝ} {d : ℝ} :
    aux_gb_glue s f d g s = d := by
  simp [aux_gb_glue]

lemma aux_gb_glue_gt {s v : ℕ} {f g : ℕ → ℝ} {d : ℝ} (h : s < v) :
    aux_gb_glue s f d g v = g (v - (s + 1)) := by
  have h1 : ¬ v < s := by omega
  have h2 : v ≠ s := by omega
  simp [aux_gb_glue, h1, h2]

lemma aux_gb_walk {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ} (hφ : aux_gb_Lip E φ)
    {x y : ℕ} {c : ℝ} (h : WalkCost E x y c) : |φ x - φ y| ≤ c := by
  induction h with
  | nil x => simp
  | @cons x y z w c he _ ih =>
    have hxy : |φ x - φ y| ≤ w := by
      rcases he with he | he
      · exact hφ _ he
      · have := hφ _ he
        simpa [abs_sub_comm] using this
    calc |φ x - φ z| ≤ |φ x - φ y| + |φ y - φ z| := abs_sub_le _ _ _
      _ ≤ w + c := add_le_add hxy ih

/-! Facts about `ell`. -/

lemma aux_gb_ell_ge1 (j : ℕ) : 1 ≤ ell j := by
  unfold ell
  have h2 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> linarith

lemma aux_gb_ell_rec (j : ℕ) : ell (j + 2) = 2 * ell j + ell (j + 1) - 1 := by
  unfold ell
  rw [pow_succ, pow_succ, pow_succ (-1 : ℝ), pow_succ (-1 : ℝ)]
  ring

lemma aux_gb_ell_bounds (j : ℕ) : 2 * ell j - 1 ≤ ell (j + 1) ∧ ell (j + 1) ≤ 2 * ell j := by
  unfold ell
  rw [pow_succ, pow_succ (-1 : ℝ)]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> constructor <;> linarith

lemma aux_gb_ell_ge2 (j : ℕ) : 2 ≤ ell (j + 1) := by
  cases j with
  | zero => norm_num [ell]
  | succ k =>
    rw [aux_gb_ell_rec k]
    have := aux_gb_ell_ge1 k
    have := aux_gb_ell_ge1 (k + 1)
    linarith

/-! Facts about the node numbering. -/

lemma aux_gb_nn (i : ℕ) :
    numNodes (i + 2) - 1 = 2 * numNodes (i + 1) ∧ middle (i + 2) = numNodes (i + 1) ∧
      middle (i + 1) < numNodes (i + 1) ∧ 1 ≤ numNodes (i + 1) := by
  unfold numNodes middle
  have h1 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by ring
  have h2 : 2 ^ (i + 2 + 1) = 2 * (2 * 2 ^ (i + 1)) := by ring
  have h3 : 1 ≤ 2 ^ (i + 1) := Nat.one_le_two_pow
  rw [show i + 2 = i + 1 + 1 from rfl] at *
  generalize 2 ^ (i + 1) = k at *
  omega

lemma aux_gb_F_prop (i : ℕ) : ∀ e ∈ edgesF (i + 1),
    e.1 < numNodes (i + 1) ∧ e.2.1 < numNodes (i + 1) ∧ 0 ≤ e.2.2 := by
  induction i with
  | zero =>
    intro e he
    simp only [edgesF, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> norm_num [numNodes]
  | succ i ih =>
    obtain ⟨hA, hB, hC, hD⟩ := aux_gb_nn i
    have hl := aux_gb_ell_ge1 (i + 1)
    have hnn : numNodes (i + 1 + 1) = 2 * numNodes (i + 1) + 1 := by
      have : numNodes (i + 2) ≥ 1 := by unfold numNodes; have := @Nat.one_le_two_pow (i + 2); omega
      show numNodes (i + 2) = _
      omega
    intro e he
    rw [edgesF.eq_3] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rw [hnn]
    rcases he with (hL | ⟨e', he', rfl⟩) | rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2, h3⟩ := ih e hL
      exact ⟨by omega, by omega, h3⟩
    · obtain ⟨h1, h2, h3⟩ := ih e' he'
      exact ⟨by simp only; omega, by simp only; omega, h3⟩
    · exact ⟨by simp only; omega, by simp only; omega, by norm_num⟩
    · exact ⟨by simp only; omega, by simp only; omega, by norm_num⟩
    · exact ⟨by simp only; omega, by simp only; omega, by simp only; linarith⟩
    · exact ⟨by simp only; omega, by simp only; omega, by simp only; linarith⟩

lemma aux_gb_const_lip (i : ℕ) (c : ℝ) : aux_gb_Lip (edgesF (i + 1)) (fun _ => c) := by
  intro e he
  simpa using (aux_gb_F_prop i e he).2.2

lemma aux_gb_neg_lip {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ} (c : ℝ) (h : aux_gb_Lip E φ) :
    aux_gb_Lip E (fun v => c - φ v) := by
  intro e he
  have := h e he
  rw [show c - φ e.1 - (c - φ e.2.1) = -(φ e.1 - φ e.2.1) by ring, abs_neg]
  exact this

lemma aux_gb_add_lip {E : List (ℕ × ℕ × ℝ)} {φ : ℕ → ℝ} (c : ℝ) (h : aux_gb_Lip E φ) :
    aux_gb_Lip E (fun v => c + φ v) := by
  intro e he
  have := h e he
  rw [show c + φ e.1 - (c + φ e.2.1) = φ e.1 - φ e.2.1 by ring]
  exact this

lemma aux_gb_GtoF {j : ℕ} {φ : ℕ → ℝ} (h : aux_gb_Lip (edgesG j) φ) :
    aux_gb_Lip (edgesF j) φ ∧ |φ 0 - φ (numNodes j - 1)| ≤ 1 ∧
      |φ (middle j) - φ 0| ≤ ell j - 1 := by
  refine ⟨fun e he => h e (List.mem_append_left _ he), ?_, ?_⟩
  · exact h (0, numNodes j - 1, 1) (by simp [edgesG])
  · exact h (middle j, 0, ell j - 1) (by simp [edgesG])

lemma aux_gb_glue_lipF (i : ℕ) (f g : ℕ → ℝ) (d : ℝ)
    (hf : aux_gb_Lip (edgesF (i + 1)) f) (hg : aux_gb_Lip (edgesF (i + 1)) g)
    (h1 : |f (numNodes (i + 1) - 1) - d| ≤ 1) (h2 : |d - g 0| ≤ 1)
    (h3 : |d - g (middle (i + 1))| ≤ ell (i + 1))
    (h4 : |f (middle (i + 1)) - g 0| ≤ ell (i + 1)) :
    aux_gb_Lip (edgesF (i + 2)) (aux_gb_glue (numNodes (i + 1)) f d g) := by
  obtain ⟨hA, hB, hC, hD⟩ := aux_gb_nn i
  intro e he
  rw [edgesF.eq_3] at he
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (hL | ⟨e', he', rfl⟩) | rfl | rfl | rfl | rfl
  · obtain ⟨ha, hb, _⟩ := aux_gb_F_prop i e hL
    rw [aux_gb_glue_lt ha, aux_gb_glue_lt hb]
    exact hf e hL
  · simp only
    rw [aux_gb_glue_gt (by omega), aux_gb_glue_gt (by omega)]
    simpa using hg e' he'
  · simp only
    rw [aux_gb_glue_lt (by omega), aux_gb_glue_self]
    exact h1
  · simp only
    rw [aux_gb_glue_self, aux_gb_glue_gt (by omega)]
    simpa using h2
  · simp only
    rw [aux_gb_glue_self, aux_gb_glue_gt (by omega)]
    simpa using h3
  · simp only
    rw [aux_gb_glue_lt hC, aux_gb_glue_gt (by omega)]
    simpa using h4

lemma aux_gb_glue_lipG (i : ℕ) (f g : ℕ → ℝ) (d : ℝ)
    (hf : aux_gb_Lip (edgesF (i + 1)) f) (hg : aux_gb_Lip (edgesF (i + 1)) g)
    (h1 : |f (numNodes (i + 1) - 1) - d| ≤ 1) (h2 : |d - g 0| ≤ 1)
    (h3 : |d - g (middle (i + 1))| ≤ ell (i + 1))
    (h4 : |f (middle (i + 1)) - g 0| ≤ ell (i + 1))
    (h5 : |f 0 - g (numNodes (i + 1) - 1)| ≤ 1)
    (h6 : |d - f 0| ≤ ell (i + 2) - 1) :
    aux_gb_Lip (edgesG (i + 2)) (aux_gb_glue (numNodes (i + 1)) f d g) := by
  obtain ⟨hA, hB, hC, hD⟩ := aux_gb_nn i
  have hF := aux_gb_glue_lipF i f g d hf hg h1 h2 h3 h4
  intro e he
  unfold edgesG at he
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with hL | rfl | rfl
  · exact hF e hL
  · simp only
    rw [hA, aux_gb_glue_lt (by omega), aux_gb_glue_gt (by omega)]
    have : 2 * numNodes (i + 1) - (numNodes (i + 1) + 1) = numNodes (i + 1) - 1 := by omega
    rw [this]
    exact h5
  · simp only
    rw [hB, aux_gb_glue_self, aux_gb_glue_lt (by omega)]
    exact h6

/-! The "distance from the start node" potential on `F_i`. -/

noncomputable def aux_gb_alpha : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | 1 => fun v => if v = 0 then 0 else 1
  | i + 2 => aux_gb_glue (numNodes (i + 1)) (aux_gb_alpha (i + 1)) (ell (i + 2) - 1)
      (fun v => 2 * ell (i + 1) - 1 + aux_gb_alpha (i + 1) v)

lemma aux_gb_alpha_prop (i : ℕ) :
    aux_gb_Lip (edgesF (i + 1)) (aux_gb_alpha (i + 1)) ∧ aux_gb_alpha (i + 1) 0 = 0 ∧
      aux_gb_alpha (i + 1) (middle (i + 1)) = ell (i + 1) - 1 ∧
      aux_gb_alpha (i + 1) (numNodes (i + 1) - 1) = ell (i + 2) - 2 := by
  induction i with
  | zero =>
    have e1 : ell 1 = 2 := by norm_num [ell]
    have e2 : ell 2 = 3 := by norm_num [ell]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [edgesF, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> norm_num [aux_gb_alpha]
    · simp [aux_gb_alpha]
    · simp [aux_gb_alpha, middle, e1]; norm_num
    · simp [aux_gb_alpha, numNodes, e2]; norm_num
  | succ i ih =>
    obtain ⟨hlip, h0, hm, hc⟩ := ih
    obtain ⟨hA, hB, hC, hD⟩ := aux_gb_nn i
    obtain ⟨hb1, hb2⟩ := aux_gb_ell_bounds (i + 1)
    have hl1 := aux_gb_ell_ge1 (i + 1)
    have hrec := aux_gb_ell_rec (i + 1)
    have hdef : aux_gb_alpha (i + 1 + 1) = aux_gb_glue (numNodes (i + 1)) (aux_gb_alpha (i + 1))
        (ell (i + 2) - 1) (fun v => 2 * ell (i + 1) - 1 + aux_gb_alpha (i + 1) v) := by
      rfl
    rw [hdef]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply aux_gb_glue_lipF i _ _ _ hlip (aux_gb_add_lip _ hlip)
      · rw [hc, abs_le]; constructor <;> linarith
      · rw [h0, abs_le]; constructor <;> linarith
      · rw [hm, abs_le]; constructor <;> linarith
      · rw [hm, h0, abs_le]; constructor <;> linarith
    · rw [aux_gb_glue_lt (by omega), h0]
    · show _ = ell (i + 2) - 1
      rw [hB, aux_gb_glue_self]
    · show _ = ell (i + 3) - 2
      rw [show i + 1 + 1 = i + 2 from rfl, hA, aux_gb_glue_gt (by omega)]
      have : 2 * numNodes (i + 1) - (numNodes (i + 1) + 1) = numNodes (i + 1) - 1 := by omega
      simp only [this, hc]
      rw [show i + 3 = i + 1 + 2 from rfl, hrec]
      ring

/-! The main potential statement. -/

lemma aux_gb_main (i : ℕ) : ∀ e ∈ edgesG (i + 1),
    ∃ φ : ℕ → ℝ, aux_gb_Lip (edgesG (i + 1)) φ ∧ e.2.2 ≤ φ e.1 - φ e.2.1 := by
  induction i with
  | zero =>
    have e1 : ell 1 = 2 := by norm_num [ell]
    have hw : ∀ e ∈ edgesG 1, e.2.2 = 1 ∧ e.1 ≠ e.2.1 := by
      intro e he
      simp only [edgesG, edgesF, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with (rfl | rfl | rfl) | rfl | rfl <;> norm_num [numNodes, middle, e1]
    intro e he
    refine ⟨fun v => if v = e.1 then 1 else 0, ?_, ?_⟩
    · intro e' he'
      rw [(hw e' he').1]
      by_cases h1 : e'.1 = e.1 <;> by_cases h2 : e'.2.1 = e.1 <;> simp [h1, h2]
    · rw [(hw e he).1]
      simp [(hw e he).2.symm]
  | succ i ih =>
    obtain ⟨hA, hB, hC, hD⟩ := aux_gb_nn i
    obtain ⟨hb1, hb2⟩ := aux_gb_ell_bounds (i + 1)
    have hl1 := aux_gb_ell_ge1 (i + 1)
    have hl2 := aux_gb_ell_ge2 (i + 1)
    obtain ⟨αL, α0, αm, αc⟩ := aux_gb_alpha_prop i
    -- the potential for the edge `(middle, start)` of `G_{i+1}`
    obtain ⟨ψ, hψ, hψw⟩ := ih (middle (i + 1), 0, ell (i + 1) - 1) (by simp [edgesG])
    obtain ⟨hψF, hψ1, hψ2⟩ := aux_gb_GtoF hψ
    obtain ⟨hψ1a, hψ1b⟩ := abs_le.mp hψ1
    obtain ⟨hψ2a, hψ2b⟩ := abs_le.mp hψ2
    simp only at hψw
    intro e he
    show ∃ φ : ℕ → ℝ, aux_gb_Lip (edgesG (i + 2)) φ ∧ e.2.2 ≤ φ e.1 - φ e.2.1
    unfold edgesG at he
    rw [edgesF.eq_3] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (((hL | ⟨e', he', rfl⟩) | rfl | rfl | rfl | rfl) | rfl | rfl)
    · -- left copy
      obtain ⟨θ, hθ, hθw⟩ := ih e (List.mem_append_left _ hL)
      obtain ⟨hθF, hθ1, hθ2⟩ := aux_gb_GtoF hθ
      obtain ⟨hθ1a, hθ1b⟩ := abs_le.mp hθ1
      obtain ⟨hθ2a, hθ2b⟩ := abs_le.mp hθ2
      obtain ⟨ha, hb, _⟩ := aux_gb_F_prop i e hL
      refine ⟨aux_gb_glue (numNodes (i + 1)) θ (θ (numNodes (i + 1) - 1)) (fun _ => θ 0),
        ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ hθF (aux_gb_const_lip i _)
        · simp
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · simp
        · rw [abs_le]; constructor <;> linarith
      · rw [aux_gb_glue_lt ha, aux_gb_glue_lt hb]
        exact hθw
    · -- right copy
      obtain ⟨θ, hθ, hθw⟩ := ih e' (List.mem_append_left _ he')
      obtain ⟨hθF, hθ1, hθ2⟩ := aux_gb_GtoF hθ
      obtain ⟨hθ1a, hθ1b⟩ := abs_le.mp hθ1
      obtain ⟨hθ2a, hθ2b⟩ := abs_le.mp hθ2
      refine ⟨aux_gb_glue (numNodes (i + 1)) (fun _ => θ 0) (θ 0) θ, ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ (aux_gb_const_lip i _) hθF
        · simp
        · simp
        · rw [abs_le]; constructor <;> linarith
        · simp; linarith
        · rw [abs_le]; constructor <;> linarith
        · simp; linarith
      · simp only
        rw [aux_gb_glue_gt (by omega), aux_gb_glue_gt (by omega)]
        simpa using hθw
    · -- edge (C, D, 1)
      refine ⟨aux_gb_glue (numNodes (i + 1)) (fun _ => 1) 0 (fun _ => 0), ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ (aux_gb_const_lip i _) (aux_gb_const_lip i _)
        · simp
        · simp
        · simp; linarith
        · simp; linarith
        · simp
        · simp; linarith
      · simp only
        rw [aux_gb_glue_lt (by omega), aux_gb_glue_self]
        norm_num
    · -- edge (D, E, 1)
      refine ⟨aux_gb_glue (numNodes (i + 1)) (fun _ => 1) 1 (fun _ => 0), ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ (aux_gb_const_lip i _) (aux_gb_const_lip i _)
        · simp
        · simp
        · simp; linarith
        · simp; linarith
        · simp
        · simp; linarith
      · simp only
        rw [aux_gb_glue_self, aux_gb_glue_gt (by omega)]
        norm_num
    · -- edge (D, F, l_i)
      refine ⟨aux_gb_glue (numNodes (i + 1)) (fun _ => -ψ 0) (1 - ψ 0) (fun v => -ψ v),
        ?_, ?_⟩
      · have hneg : aux_gb_Lip (edgesF (i + 1)) (fun v => -ψ v) := by
          have := aux_gb_neg_lip 0 hψF
          simpa using this
        apply aux_gb_glue_lipG i _ _ _ (aux_gb_const_lip i _) hneg
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · simp; linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      · simp only
        rw [aux_gb_glue_self, aux_gb_glue_gt (by omega)]
        simp only [Nat.add_sub_cancel_left]
        linarith
    · -- edge (B, E, l_i)
      refine ⟨aux_gb_glue (numNodes (i + 1)) ψ (ψ 0) (fun _ => ψ 0 - 1), ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ hψF (aux_gb_const_lip i _)
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      · simp only
        rw [aux_gb_glue_lt hC, aux_gb_glue_gt (by omega)]
        linarith
    · -- edge (A, right node, 1)
      refine ⟨aux_gb_glue (numNodes (i + 1)) (fun _ => 1) 1 (fun _ => 0), ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ (aux_gb_const_lip i _) (aux_gb_const_lip i _)
        · simp
        · simp
        · simp; linarith
        · simp; linarith
        · simp
        · simp; linarith
      · simp only
        rw [hA, aux_gb_glue_lt (by omega), aux_gb_glue_gt (by omega)]
        norm_num
    · -- edge (middle, start, l_{i+1} - 1)
      refine ⟨aux_gb_glue (numNodes (i + 1)) (aux_gb_alpha (i + 1)) (ell (i + 2) - 1)
        (fun v => ell (i + 2) - 2 - aux_gb_alpha (i + 1) v), ?_, ?_⟩
      · apply aux_gb_glue_lipG i _ _ _ αL (aux_gb_neg_lip _ αL)
        · rw [αc, abs_le]; constructor <;> linarith
        · rw [α0, abs_le]; constructor <;> linarith
        · rw [αm, abs_le]; constructor <;> linarith
        · rw [αm, α0, abs_le]; constructor <;> linarith
        · rw [αc, α0, abs_le]; constructor <;> linarith
        · rw [α0, abs_le]; constructor <;> linarith
      · simp only
        rw [hB, aux_gb_glue_self, aux_gb_glue_lt (by omega), α0]
        linarith

end TSPHeuristics.NNLower

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 1 ≤ i) :
    ∀ e ∈ edgesG i, spDist (edgesG i) e.1 e.2.1 = e.2.2 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rintro ⟨a, b, w⟩ he
  obtain ⟨φ, hφ, hw⟩ := aux_gb_main j (a, b, w) he
  simp only at hw ⊢
  unfold spDist
  apply IsLeast.csInf_eq
  constructor
  · have := WalkCost.cons (E := edgesG (j + 1)) (Or.inl he) (WalkCost.nil b)
    simpa using this
  · intro c hc
    exact le_trans hw (le_trans (le_abs_self _) (aux_gb_walk hφ hc))
