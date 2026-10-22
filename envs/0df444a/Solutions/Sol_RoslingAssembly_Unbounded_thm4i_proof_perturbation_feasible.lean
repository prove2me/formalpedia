-- Prove2me | solution 1 for RoslingAssembly.Unbounded.thm4i_proof_perturbation_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:55:09.265983+00:00
-- url     : https://prove2.me/submissions/40a91bfa-6f4e-4035-a20e-e400c895d397

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb



namespace RoslingAssembly.Unbounded

open MeasureTheory

namespace Model

variable (S : Model)

lemma succ_lt_of_mem (hT : S.IsTree) {y : ℕ} (hy : y ∈ S.items) : S.succ y + 1 ≤ y := by
  obtain ⟨h1, h2, h3⟩ := hT
  simp only [Model.items, Finset.mem_Icc] at hy
  by_cases hy1 : y = 1
  · subst hy1; simp [h2]
  · have := h3 y (by simp only [Finset.mem_Icc]; omega)
    omega

lemma succ_mem_of_ne_one (hT : S.IsTree) {y : ℕ} (hy : y ∈ S.items) (hy1 : y ≠ 1) :
    S.succ y ∈ S.items := by
  obtain ⟨h1, h2, h3⟩ := hT
  simp only [Model.items, Finset.mem_Icc] at hy ⊢
  have := h3 y (by simp only [Finset.mem_Icc]; omega)
  omega

lemma iter_le (hT : S.IsTree) (x : ℕ) :
    ∀ m, (∀ m' ∈ Finset.range m, S.succ^[m'] x ∈ S.items) → S.succ^[m] x + m ≤ x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (fun m' hm' => h m' (by simp only [Finset.mem_range] at hm' ⊢; omega))
    have h2 := h m (by simp)
    have h3 := S.succ_lt_of_mem hT h2
    rw [Function.iterate_succ_apply']
    omega

open Classical in
lemma A_sub (j : ℕ) : S.A j ⊆ S.items := by
  unfold Model.A; exact @Finset.filter_subset _ _ (fun _ => Classical.propDecidable _) _

open Classical in
lemma mem_A_iff (j k : ℕ) : k ∈ S.A j ↔ k ∈ S.items ∧
    ∃ n ∈ Finset.Icc 1 S.N, S.succ^[n] j = k ∧ ∀ m ∈ Finset.range n, S.succ^[m] j ∈ S.items := by
  unfold Model.A; exact @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _

lemma mem_A_lt (hT : S.IsTree) {j k : ℕ} (hk : k ∈ S.A j) : k < j := by
  rw [S.mem_A_iff] at hk
  simp only [Finset.mem_Icc] at hk
  obtain ⟨_, n, ⟨hn1, _⟩, hnk, hch⟩ := hk
  have := S.iter_le hT j n hch
  rw [hnk] at this
  omega

lemma A_one (hT : S.IsTree) : S.A 1 = ∅ := by
  ext k
  simp only [Finset.notMem_empty, iff_false]
  intro hk
  have := S.mem_A_lt hT hk
  have h1 := hT.1
  have hk2 : k ∈ S.items := S.A_sub 1 hk
  simp only [Model.items, Finset.mem_Icc] at hk2
  omega

lemma A_succ (hT : S.IsTree) {j : ℕ} (hj : j ∈ S.items) (hs : S.succ j ∈ S.items) :
    S.A j = insert (S.succ j) (S.A (S.succ j)) := by
  have hjs := S.succ_lt_of_mem hT hj
  have hN : j ≤ S.N := by simpa [Model.items] using (Finset.mem_Icc.mp hj).2
  ext k
  rw [Finset.mem_insert, S.mem_A_iff, S.mem_A_iff]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hk, n, ⟨hn1, hnN⟩, hnk, hch⟩
    by_cases hn : n = 1
    · subst hn
      left
      simpa using hnk.symm
    · right
      refine ⟨hk, n - 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · have : n = (n - 1) + 1 := by omega
        rw [← hnk, this, Function.iterate_succ_apply]
        simp
      · intro m hm
        have := hch (m + 1) (by simp only [Finset.mem_range] at hm ⊢; omega)
        rwa [Function.iterate_succ_apply] at this
  · rintro (h | ⟨hk, n, ⟨hn1, hnN⟩, hnk, hch⟩)
    · refine ⟨h ▸ hs, 1, ⟨le_rfl, ?_⟩, by simp [h], ?_⟩
      · have := hT.1; omega
      · intro m hm
        have : m = 0 := by simp only [Finset.mem_range] at hm; omega
        subst this
        simpa using hj
    · have hle := S.iter_le hT _ n hch
      rw [hnk] at hle
      have hk1 : 1 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        exact this
      refine ⟨hk, n + 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]; exact hnk
      · intro m hm
        cases m with
        | zero => simpa using hj
        | succ m =>
          rw [Function.iterate_succ_apply]
          exact hch m (by simp only [Finset.mem_range] at hm ⊢; omega)

lemma M_succ (hT : S.IsTree) {j : ℕ} (hj : j ∈ S.items) :
    S.M j = S.l j + S.M (S.succ j) := by
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1; omega
  by_cases hs : S.succ j ∈ S.items
  · have hs0 : S.succ j ≠ 0 := by
      have := (Finset.mem_Icc.mp hs).1; omega
    have hnot : S.succ j ∉ S.A (S.succ j) := fun h => by
      have := S.mem_A_lt hT h; omega
    unfold Model.M
    rw [if_neg hj0, if_neg hs0, S.A_succ hT hj hs, Finset.sum_insert hnot]
  · have hj1 : j = 1 := by
      by_contra hne
      exact hs (S.succ_mem_of_ne_one hT hj hne)
    subst hj1
    unfold Model.M
    rw [S.A_one hT, hT.2.1]
    simp

open Classical in
lemma mem_B_iff (i k : ℕ) : k ∈ S.B i ↔ k ∈ S.items ∧ i ∈ S.A k := by
  simp [Model.B]

lemma B_sub (i : ℕ) : S.B i ⊆ S.items := fun k hk => ((S.mem_B_iff i k).mp hk).1

lemma mem_P_iff (i j : ℕ) : j ∈ S.P i ↔ j ∈ S.items ∧ S.succ j = i := by
  unfold Model.P; exact Finset.mem_filter

lemma P_mem_B (hT : S.IsTree) {i : ℕ} (hi : i ∈ S.items) {i' : ℕ}
    (hi' : i' ∈ insert i (S.B i)) {j : ℕ} (hj : j ∈ S.P i') : j ∈ S.B i := by
  rw [S.mem_P_iff] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hi'i : i' ∈ S.items := by
    rcases Finset.mem_insert.mp hi' with h | h
    · rw [h]; exact hi
    · exact S.B_sub i h
  rw [S.mem_B_iff]
  refine ⟨hj1, ?_⟩
  rw [S.A_succ hT hj1 (hj2 ▸ hi'i), hj2]
  rcases Finset.mem_insert.mp hi' with h | h
  · rw [h]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((S.mem_B_iff i i').mp h).2

/-- the extra amount ordered of item `j` in Lean period `k` -/
noncomputable def ext (i : ℕ) (δ : ℝ) (j k : ℕ) : ℝ :=
  open Classical in if j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ k then δ else 0

lemma perturb_apply (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (k : ℕ)
    (x : Fin k → ℝ) (j : ℕ) : S.perturb π i δ k x j = π k x j + S.ext i δ j k := by
  unfold Model.perturb Model.ext
  congr 1

lemma ext_nonneg (i : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (j k : ℕ) : 0 ≤ S.ext i δ j k := by
  unfold Model.ext; split_ifs <;> simp [hδ]

lemma ext_mono (i : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) {a b : ℕ} (hab : a ≤ b) :
    S.ext i δ j a ≤ S.ext i δ j b := by
  unfold Model.ext
  by_cases h : j ∈ insert i (S.B i) ∧ S.Mmax i - S.M j ≤ a
  · rw [if_pos h, if_pos ⟨h.1, by omega⟩]
  · rw [if_neg h]; split_ifs <;> simp [hδ]

lemma Y_perturb (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ) (ω : ℕ → ℝ) (k j : ℕ) :
    Y (S.perturb π i δ) ω k j = Y π ω k j + S.ext i δ j k := by
  unfold Y; rw [S.perturb_apply]

lemma pos_perturb (x0 : ℕ → ℕ → ℝ) (π : RoslingAssembly.SeriesEquiv.Policy) (i : ℕ) (δ : ℝ)
    (ω : ℕ → ℝ) (j k s : ℕ) :
    pos x0 (S.perturb π i δ) ω j k s =
      pos x0 π ω j k s + (if s ≤ k then S.ext i δ j (k - s) else 0) := by
  unfold pos
  by_cases h : s ≤ k
  · simp only [if_pos h, S.Y_perturb]; ring
  · simp only [if_neg h]; ring

theorem perturbation_feasible_core (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (i : ℕ) (hi : i ∈ S.items) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π)
    (hπ : S.Feasible x0 π) :
    IsMeasurablePolicy (S.perturb π i δ) ∧ S.Feasible x0 (S.perturb π i δ) := by
  refine ⟨?_, ?_⟩
  · intro k j
    have : (fun x : Fin k → ℝ => S.perturb π i δ k x j) = fun x => π k x j + S.ext i δ j k := by
      funext x; exact S.perturb_apply π i δ k x j
    rw [this]
    exact (hπm k j).add measurable_const
  · unfold Model.Feasible at hπ ⊢
    filter_upwards [hπ] with ω hω k i' hi'
    obtain ⟨h1, h2⟩ := hω k i' hi'
    refine ⟨?_, ?_⟩
    · rw [S.pos_perturb, S.Y_perturb]
      have e1 := S.ext_nonneg i hδ i' k
      split_ifs with hk
      · have := S.ext_mono i hδ i' (a := k - 1) (b := k) (by omega)
        linarith
      · linarith
    · intro j hj
      rw [S.Y_perturb, S.pos_perturb]
      have key : S.ext i δ i' k ≤ (if S.l j ≤ k then S.ext i δ j (k - S.l j) else 0) := by
        by_cases hc : i' ∈ insert i (S.B i) ∧ S.Mmax i - S.M i' ≤ k
        · have hjB := S.P_mem_B hT hi hc.1 hj
          have hjM := S.M_succ hT (((S.mem_P_iff i' j).mp hj).1)
          rw [((S.mem_P_iff i' j).mp hj).2] at hjM
          have hmax : S.M j ≤ S.Mmax i :=
            Finset.le_sup (f := S.M) (Finset.mem_insert_of_mem hjB)
          have hlk : S.l j ≤ k := by omega
          rw [if_pos hlk]
          unfold Model.ext
          rw [if_pos hc, if_pos ⟨Finset.mem_insert_of_mem hjB, by omega⟩]
        · have : S.ext i δ i' k = 0 := by unfold Model.ext; rw [if_neg hc]
          rw [this]
          split_ifs
          · exact S.ext_nonneg i hδ _ _
          · exact le_rfl
      have h3 := h2 j hj
      linarith

end Model
end RoslingAssembly.Unbounded

open RoslingAssembly.Unbounded
open MeasureTheory

theorem solution (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (hπ : S.Feasible x0 π) :
    IsMeasurablePolicy (S.perturb π i δ) ∧ S.Feasible x0 (S.perturb π i δ) := by
  exact S.perturbation_feasible_core x0 hT i hi δ hδ π hπm hπ
