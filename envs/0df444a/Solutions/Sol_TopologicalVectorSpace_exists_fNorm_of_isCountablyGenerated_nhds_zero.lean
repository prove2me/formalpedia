-- Prove2me | solution 1 for TopologicalVectorSpace.exists_fNorm_of_isCountablyGenerated_nhds_zero
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:13:43.627093+00:00
-- url     : https://prove2.me/submissions/ce2a19e9-8095-4b5a-8c9c-a8bf1fcf61ac

import Mathlib

open Topology

set_option autoImplicit false

namespace Sol_TopologicalVectorSpace_exists_fNorm_of_isCountablyGenerated_nhds_zero

open scoped NNReal

/-- The "level" of a predicate on `ℕ`: `2⁻ᵐ` where `m` is the first index at which `P` fails,
and `0` if `P` holds everywhere. -/
noncomputable def lev (P : ℕ → Prop) : ℝ≥0 :=
  open Classical in if h : ∃ n, ¬ P n then (2⁻¹ : ℝ≥0) ^ (Nat.find h) else 0

lemma half_pos : (0 : ℝ≥0) < 2⁻¹ := by positivity

lemma half_lt_one : (2⁻¹ : ℝ≥0) < 1 := by
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

lemma lev_lt_iff {P : ℕ → Prop} (hP : ∀ m n, m ≤ n → P n → P m) (n : ℕ) :
    lev P < (2⁻¹ : ℝ≥0) ^ n ↔ P n := by
  classical
  unfold lev
  split_ifs with h
  · rw [pow_lt_pow_iff_right_of_lt_one₀ half_pos half_lt_one, Nat.lt_find_iff]
    constructor
    · intro H
      exact not_not.mp (H n le_rfl)
    · intro H m hm
      exact not_not.mpr (hP m n hm H)
  · have hn : P n := not_not.mp (fun hn => h ⟨n, hn⟩)
    exact iff_of_true (pow_pos half_pos n) hn

lemma lev_eq_zero_or (P : ℕ → Prop) : lev P = 0 ∨ ∃ m, lev P = (2⁻¹ : ℝ≥0) ^ m := by
  classical
  unfold lev
  split_ifs with h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

lemma lev_mono {P Q : ℕ → Prop} (hP : ∀ m n, m ≤ n → P n → P m)
    (hQ : ∀ m n, m ≤ n → Q n → Q m) (h : ∀ n, Q n → P n) : lev P ≤ lev Q := by
  by_contra hlt
  rw [not_le] at hlt
  rcases lev_eq_zero_or P with h0 | ⟨m, hm⟩
  · rw [h0] at hlt
    exact not_lt_zero hlt
  · rw [hm] at hlt
    have h1 : Q m := (lev_lt_iff hQ m).1 hlt
    have h2 : lev P < (2⁻¹ : ℝ≥0) ^ m := (lev_lt_iff hP m).2 (h m h1)
    rw [hm] at h2
    exact lt_irrefl _ h2

lemma sum_zipWith_le {X : Type*} (d d' : X → X → ℝ≥0) (h : ∀ a b, d' a b ≤ d a b) :
    ∀ l₁ l₂ : List X, (List.zipWith d' l₁ l₂).sum ≤ (List.zipWith d l₁ l₂).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
      simp only [List.zipWith_cons_cons, List.sum_cons]
      exact add_le_add (h a b) (sum_zipWith_le d d' h l₁ l₂)

/-- A map which does not increase the pre-distance `d` does not increase the associated
chain pseudo-distance. -/
lemma dist_map_le {X : Type*} (d : X → X → ℝ≥0) (h0 : ∀ x, d x x = 0)
    (hc : ∀ x y, d x y = d y x) (f : X → X) (hf : ∀ a b, d (f a) (f b) ≤ d a b) (x y : X) :
    @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d h0 hc)) (f x) (f y) ≤
      @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d h0 hc)) x y := by
  rw [PseudoMetricSpace.dist_ofPreNNDist, PseudoMetricSpace.dist_ofPreNNDist, NNReal.coe_le_coe]
  refine le_ciInf fun l => ?_
  refine (ciInf_le (OrderBot.bddBelow _) (l.map f)).trans ?_
  have hrw : List.zipWith d (f x :: l.map f) (l.map f ++ [f y]) =
      List.zipWith (fun a b => d (f a) (f b)) (x :: l) (l ++ [y]) := by
    have e1 : f x :: l.map f = (x :: l).map f := by simp
    have e2 : l.map f ++ [f y] = (l ++ [y]).map f := by simp
    rw [e1, e2, List.zipWith_map]
  rw [hrw]
  exact sum_zipWith_le _ _ hf _ _

/-- A decreasing base of balanced `0`-neighbourhoods `V n` with `V (n+1) + V (n+1) + V (n+1) ⊆ V n`. -/
lemma exists_seq (𝕜 : Type*) {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    (hE : (𝓝 (0 : E)).IsCountablyGenerated) :
    ∃ V : ℕ → Set E, (𝓝 (0 : E)).HasBasis (fun _ => True) V ∧ (∀ m n, m ≤ n → V n ⊆ V m) ∧
      (∀ n, Balanced 𝕜 (V n)) ∧
      (∀ n, ∀ a ∈ V (n + 1), ∀ b ∈ V (n + 1), ∀ c ∈ V (n + 1), a + b + c ∈ V n) := by
  have := hE
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have key : ∀ (n : ℕ) (s : Set E), s ∈ 𝓝 (0 : E) → ∃ t : Set E, t ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 t ∧
      t ⊆ U n ∧ t ⊆ s ∧ ∀ a ∈ t, ∀ b ∈ t, ∀ c ∈ t, a + b + c ∈ s := by
    intro n s hs
    obtain ⟨W, hW, hW4⟩ := exists_nhds_zero_quarter hs
    have h1 : W ∩ U n ∩ s ∈ 𝓝 (0 : E) :=
      Filter.inter_mem (Filter.inter_mem hW (hU.1.mem_of_mem trivial)) hs
    obtain ⟨t, ⟨ht, htb⟩, hts⟩ := (nhds_basis_balanced 𝕜 E).mem_iff.1 h1
    refine ⟨t, ht, htb, fun x hx => (hts hx).1.2, fun x hx => (hts hx).2,
      fun a ha b hb c hc => ?_⟩
    have h4 := hW4 (hts ha).1.1 (hts hb).1.1 (hts hc).1.1 (mem_of_mem_nhds hW)
    simpa using h4
  choose! F hF using key
  let V : ℕ → Set E := fun n => Nat.rec (F 0 Set.univ) (fun k s => F (k + 1) s) n
  have hV0 : V 0 = F 0 Set.univ := rfl
  have hVs : ∀ n, V (n + 1) = F (n + 1) (V n) := fun n => rfl
  have hVn : ∀ n, V n ∈ 𝓝 (0 : E) := by
    intro n
    induction n with
    | zero => rw [hV0]; exact (hF 0 _ Filter.univ_mem).1
    | succ k ih => rw [hVs]; exact (hF _ _ ih).1
  have hVU : ∀ n, V n ⊆ U n := by
    intro n
    cases n with
    | zero => rw [hV0]; exact (hF 0 _ Filter.univ_mem).2.2.1
    | succ k => rw [hVs]; exact (hF _ _ (hVn k)).2.2.1
  have hVstep : ∀ n, V (n + 1) ⊆ V n := by
    intro n
    rw [hVs]
    exact (hF _ _ (hVn n)).2.2.2.1
  have hVanti : ∀ m n, m ≤ n → V n ⊆ V m := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step _ ih => exact (hVstep _).trans ih
  refine ⟨V, ?_, hVanti, ?_, ?_⟩
  · refine ⟨fun s => ⟨fun hs => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (hVn n) hn⟩⟩
    obtain ⟨n, -, hn⟩ := hU.1.mem_iff.1 hs
    exact ⟨n, trivial, (hVU n).trans hn⟩
  · intro n
    cases n with
    | zero => rw [hV0]; exact (hF 0 _ Filter.univ_mem).2.1
    | succ k => rw [hVs]; exact (hF _ _ (hVn k)).2.1
  · intro n a ha b hb c hc
    rw [hVs] at ha hb hc
    exact (hF _ _ (hVn n)).2.2.2.2 a ha b hb c hc

end Sol_TopologicalVectorSpace_exists_fNorm_of_isCountablyGenerated_nhds_zero

open Sol_TopologicalVectorSpace_exists_fNorm_of_isCountablyGenerated_nhds_zero in
theorem solution (𝕜 : Type*) {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    (hE : (𝓝 (0 : E)).IsCountablyGenerated) :
    ∃ N : E → ℝ, (∀ x, N x = 0 ↔ x = 0) ∧ (∀ x y, N (x + y) ≤ N x + N y) ∧
      (∀ (c : 𝕜) (x : E), ‖c‖ ≤ 1 → N (c • x) ≤ N x) ∧
      (𝓝 (0 : E)).HasBasis (fun ε : ℝ => 0 < ε) (fun ε => {x | N x < ε}) := by
  obtain ⟨V, hVb, hVanti, hVbal, hV3⟩ := exists_seq 𝕜 hE
  -- the gauge `g x = 2⁻ᵐ`, `m` the first index with `x ∉ V m` (and `0` if there is none)
  have hP : ∀ (x : E) (m n : ℕ), m ≤ n → x ∈ V n → x ∈ V m := fun x m n hmn h => hVanti m n hmn h
  obtain ⟨g, hg⟩ : ∃ g : E → NNReal, ∀ x, g x = lev (fun n => x ∈ V n) := ⟨_, fun _ => rfl⟩
  have hg_lt : ∀ x n, g x < (2⁻¹ : NNReal) ^ n ↔ x ∈ V n := by
    intro x n
    rw [hg]
    exact lev_lt_iff (hP x) n
  have hg_val : ∀ x, g x = 0 ∨ ∃ m, g x = (2⁻¹ : NNReal) ^ m := by
    intro x
    rw [hg]
    exact lev_eq_zero_or _
  have hg_zero : g 0 = 0 := by
    rcases hg_val 0 with h | ⟨m, hm⟩
    · exact h
    · exfalso
      have h1 := (hg_lt 0 m).2 (mem_of_mem_nhds (hVb.mem_of_mem trivial))
      rw [hm] at h1
      exact lt_irrefl _ h1
  have hg_smul : ∀ (c : 𝕜) (x : E), ‖c‖ ≤ 1 → g (c • x) ≤ g x := by
    intro c x hc
    rw [hg, hg]
    exact lev_mono (hP _) (hP _) (fun n hn => (hVbal n).smul_mem hc hn)
  have hg_neg_le : ∀ x : E, g (-x) ≤ g x := by
    intro x
    have h1 := hg_smul (-1 : 𝕜) x (by simp)
    rwa [neg_one_smul] at h1
  have hg_neg : ∀ x : E, g (-x) = g x := by
    intro x
    refine le_antisymm (hg_neg_le x) ?_
    have h1 := hg_neg_le (-x)
    rwa [neg_neg] at h1
  -- the pre-distance
  obtain ⟨d, hd⟩ : ∃ d : E → E → NNReal, ∀ x y, d x y = g (x - y) := ⟨_, fun _ _ => rfl⟩
  have d_self : ∀ x, d x x = 0 := by
    intro x
    rw [hd, sub_self, hg_zero]
  have d_comm : ∀ x y, d x y = d y x := by
    intro x y
    rw [hd, hd, ← hg_neg (x - y), neg_sub]
  have hd4 : ∀ x₁ x₂ x₃ x₄, d x₁ x₄ ≤ 2 * max (d x₁ x₂) (max (d x₂ x₃) (d x₃ x₄)) := by
    intro x₁ x₂ x₃ x₄
    by_contra hlt
    rw [not_le] at hlt
    rcases hg_val (x₁ - x₄) with h0 | ⟨m, hm⟩
    · rw [hd x₁ x₄, h0] at hlt
      exact not_lt_zero hlt
    · rw [hd x₁ x₄, hm] at hlt
      have hmax : max (d x₁ x₂) (max (d x₂ x₃) (d x₃ x₄)) < (2⁻¹ : NNReal) ^ (m + 1) := by
        have h1 := mul_lt_mul_of_pos_left hlt half_pos
        rwa [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul, ← pow_succ'] at h1
      have h1 : x₁ - x₂ ∈ V (m + 1) := by
        apply (hg_lt _ _).1
        rw [← hd]
        exact (le_max_left _ _).trans_lt hmax
      have h2 : x₂ - x₃ ∈ V (m + 1) := by
        apply (hg_lt _ _).1
        rw [← hd]
        exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hmax
      have h3 : x₃ - x₄ ∈ V (m + 1) := by
        apply (hg_lt _ _).1
        rw [← hd]
        exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hmax
      have h4 := hV3 m _ h1 _ h2 _ h3
      have e : x₁ - x₂ + (x₂ - x₃) + (x₃ - x₄) = x₁ - x₄ := by abel
      rw [e] at h4
      have h5 := (hg_lt _ _).2 h4
      rw [hm] at h5
      exact lt_irrefl _ h5
  -- the chain pseudo-distance
  let I : PseudoMetricSpace E := PseudoMetricSpace.ofPreNNDist d d_self d_comm
  have hdist_le : ∀ x y, @dist E I.toDist x y ≤ d x y :=
    PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_dist : ∀ x y, (d x y : ℝ) ≤ 2 * @dist E I.toDist x y :=
    PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ hd4
  have htrans : ∀ z x y, @dist E I.toDist (x + z) (y + z) ≤ @dist E I.toDist x y := by
    intro z x y
    refine dist_map_le d d_self d_comm (fun u => u + z) (fun a b => ?_) x y
    rw [hd, hd, add_sub_add_right_eq_sub]
  have hsmul : ∀ c : 𝕜, ‖c‖ ≤ 1 → ∀ x y,
      @dist E I.toDist (c • x) (c • y) ≤ @dist E I.toDist x y := by
    intro c hc x y
    refine dist_map_le d d_self d_comm (fun u => c • u) (fun a b => ?_) x y
    rw [hd, hd, ← smul_sub]
    exact hg_smul c _ hc
  refine ⟨fun x => @dist E I.toDist x 0, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx' : @dist E I.toDist x 0 = 0 := hx
      have h1 : (d x 0 : ℝ) ≤ 0 := by
        have h := hle_dist x 0
        rwa [hx', mul_zero] at h
      have h2 : g x = 0 := by
        have h3 : d x 0 = 0 := by
          apply le_antisymm _ bot_le
          exact_mod_cast h1
        rwa [hd, sub_zero] at h3
      by_contra hne
      have hmem : ({x}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
        isOpen_compl_singleton.mem_nhds (fun h : (0 : E) = x => hne h.symm)
      obtain ⟨n, -, hn⟩ := hVb.mem_iff.1 hmem
      have hxn : x ∈ V n := (hg_lt x n).1 (by rw [h2]; exact pow_pos half_pos n)
      exact hn hxn rfl
    · intro hx
      subst hx
      exact @dist_self E I 0
  · intro x y
    have h1 : @dist E I.toDist (x + y) 0 ≤ @dist E I.toDist (x + y) y + @dist E I.toDist y 0 :=
      @dist_triangle E I _ _ _
    have h2 := htrans y x 0
    rw [zero_add] at h2
    show @dist E I.toDist (x + y) 0 ≤ @dist E I.toDist x 0 + @dist E I.toDist y 0
    linarith
  · intro c x hc
    have h := hsmul c hc x 0
    rwa [smul_zero] at h
  · refine hVb.to_hasBasis (fun n _ => ?_) (fun ε hε => ?_)
    · refine ⟨(2⁻¹ : ℝ) ^ (n + 1), by positivity, fun x hx => ?_⟩
      have hx' : @dist E I.toDist x 0 < (2⁻¹ : ℝ) ^ (n + 1) := hx
      apply (hg_lt x n).1
      have h1 := hle_dist x 0
      rw [hd, sub_zero] at h1
      have h2 : (g x : ℝ) < (2⁻¹ : ℝ) ^ n := by
        have h3 : 2 * (2⁻¹ : ℝ) ^ (n + 1) = (2⁻¹ : ℝ) ^ n := by
          rw [pow_succ]
          ring
        linarith
      rw [← NNReal.coe_lt_coe]
      push_cast
      exact h2
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
      refine ⟨n, trivial, fun x hx => ?_⟩
      have h1 : g x < (2⁻¹ : NNReal) ^ n := (hg_lt x n).2 hx
      have h2 := hdist_le x 0
      rw [hd, sub_zero] at h2
      have h3 : (g x : ℝ) < (2⁻¹ : ℝ) ^ n := by
        have h4 := NNReal.coe_lt_coe.2 h1
        push_cast at h4
        exact h4
      show @dist E I.toDist x 0 < ε
      linarith
