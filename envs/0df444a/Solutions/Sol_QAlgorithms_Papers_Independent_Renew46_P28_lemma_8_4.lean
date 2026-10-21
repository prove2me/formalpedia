-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P28.lemma_8_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:17:23.611924+00:00
-- url     : https://prove2.me/submissions/ad4e628e-ace9-424b-9718-7c8d48b8d3ac

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28
open QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w



/-- Lemma 8.4, PDF p.48, with the compatible ultrametric absolute value and
maximum norm fixed in Section 8.2, PDF p.47. The countable index set is represented
as a subset of the natural numbers, allowing finite partitions as well. -/
theorem solution
    (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [TotallyDisconnectedSpace K]
    (hultra : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (d : ℕ) (hd : 0 < d) (U : Set (Fin d → K))
    (hU : IsOpen U) (hne : U.Nonempty)
    {I : Type*} (Ui : I → Set (Fin d → K))
    (hUi : ∀ i, IsOpen (Ui i)) (hsub : ∀ i, Ui i ⊆ U)
    (hcover : U = ⋃ i, Ui i) :
    ∃ (J : Set ℕ) (r : J → ℝ) (a : J → (Fin d → K)),
      (∀ j, 0 < r j ∧ a j ∈ U) ∧
      U = ⋃ j, Metric.ball (a j) (r j) ∧
      (Pairwise fun i j : J => Disjoint (Metric.ball (a i) (r i))
        (Metric.ball (a j) (r j))) ∧
      (∀ j, ∃ i, Metric.ball (a j) (r j) ⊆ Ui i) := by
  classical
  letI : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm hultra
  haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
  haveI : SecondCountableTopology (Fin d → K) := secondCountable_of_proper
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set ρ : ℕ → ℝ := fun n => ‖c‖ ^ n with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n => pow_pos hc0 n
  have hρanti : ∀ m n, m ≤ n → ρ n ≤ ρ m := fun m n h => pow_le_pow_of_le_one hc0.le hc1.le h
  have good : ∀ x ∈ U, ∃ n, ∃ i, Metric.ball x (ρ n) ⊆ Ui i := by
    intro x hx
    rw [hcover] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hUi i) x hi
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hc1
    exact ⟨n, i, (Metric.ball_subset_ball hn.le).trans hball⟩
  let N : U → ℕ := fun x => Nat.find (good x.1 x.2)
  let B : U → Set (Fin d → K) := fun x => Metric.ball x.1 (ρ (N x))
  have hNspec : ∀ x : U, ∃ i, B x ⊆ Ui i := fun x => Nat.find_spec (good x.1 x.2)
  have hBU : ∀ x : U, B x ⊆ U := fun x => by
    obtain ⟨i, hi⟩ := hNspec x
    exact hi.trans (hsub i)
  have key0 : ∀ x y : U, N x ≤ N y → (B x ∩ B y).Nonempty → B x = B y := by
    intro x y hle ⟨z, hzx, hzy⟩
    have ex : B x = Metric.ball z (ρ (N x)) := IsUltrametricDist.ball_eq_of_mem hzx
    have ey : B y = Metric.ball z (ρ (N y)) := IsUltrametricDist.ball_eq_of_mem hzy
    have hyx : y.1 ∈ B x := by
      rw [ex]
      have : y.1 ∈ B y := Metric.mem_ball_self (hρpos _)
      rw [ey] at this
      exact Metric.ball_subset_ball (hρanti _ _ hle) this
    have eyx : Metric.ball y.1 (ρ (N x)) = B x := (IsUltrametricDist.ball_eq_of_mem hyx).symm
    have hle' : N y ≤ N x := by
      refine Nat.find_min' (good y.1 y.2) ?_
      obtain ⟨i, hi⟩ := hNspec x
      exact ⟨i, eyx ▸ hi⟩
    have hEq : N x = N y := le_antisymm hle hle'
    rw [ex, ey, hEq]
  have key : ∀ x y : U, (B x ∩ B y).Nonempty → B x = B y := by
    intro x y h
    rcases le_total (N x) (N y) with h1 | h1
    · exact key0 x y h1 h
    · exact (key0 y x h1 (by rwa [inter_comm])).symm
  have hcount : Countable (range B) := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun b : range B => (b : Set (Fin d → K)))
      ?_ ?_ ?_
    · rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩ hne
      simp only [Function.onFun]
      rw [Set.disjoint_iff_inter_eq_empty]
      by_contra h
      exact hne (Subtype.ext (key x y (Set.nonempty_iff_ne_empty.2 h)))
    · rintro ⟨_, ⟨x, rfl⟩⟩; exact Metric.isOpen_ball
    · rintro ⟨_, ⟨x, rfl⟩⟩; exact ⟨x.1, Metric.mem_ball_self (hρpos _)⟩
  obtain ⟨f, hf⟩ := hcount.exists_injective_nat
  let J : Set ℕ := range f
  have h1 : ∀ j : J, ∃ b : range B, f b = j.1 := fun j => j.2
  choose bb hbb using h1
  have h2 : ∀ b : range B, ∃ x : U, B x = b.1 := fun b => b.2
  choose xx hxx using h2
  refine ⟨J, fun j => ρ (N (xx (bb j))), fun j => (xx (bb j)).1, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hρpos _, (xx (bb j)).2⟩
  · apply Set.Subset.antisymm
    · intro x hx
      let b : range B := ⟨B ⟨x, hx⟩, ⟨_, rfl⟩⟩
      let j : J := ⟨f b, ⟨b, rfl⟩⟩
      have hb : bb j = b := hf (hbb j)
      refine mem_iUnion.2 ⟨j, ?_⟩
      show x ∈ B (xx (bb j))
      rw [hxx, hb]
      exact Metric.mem_ball_self (hρpos _)
    · exact iUnion_subset fun j => hBU _
  · intro i j hij
    have hne : (bb i) ≠ (bb j) := by
      intro h
      apply hij
      apply Subtype.ext
      rw [← hbb i, ← hbb j, h]
    show Disjoint (B (xx (bb i))) (B (xx (bb j)))
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra h
    apply hne
    apply Subtype.ext
    rw [← hxx, ← hxx]
    exact key _ _ (Set.nonempty_iff_ne_empty.2 h)
  · intro j
    exact hNspec _

