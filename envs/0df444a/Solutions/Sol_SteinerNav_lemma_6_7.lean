-- Prove2me | solution 1 for SteinerNav.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:58:06.443261+00:00
-- url     : https://prove2.me/submissions/f9e0bb5d-1518-4a82-a409-905207212645

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_GreedyRun
import Theorems.Thm_SteinerNav_descent_terminates

open SteinerNav

namespace AuxLemma67

lemma dist_bounds {d : ℕ} (P : Finset (Pt d)) (hn : 2 ≤ P.card) :
    0 < minDist P ∧ 1 ≤ aspectRatio P ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → minDist P ≤ dist x y ∧ dist x y ≤ maxDist P := by
  have h1 : 1 < P.card := by omega
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.mp h1
  let offDiag : Finset (Pt d × Pt d) := (P ×ˢ P).filter fun e => e.1 ≠ e.2
  let Dset : Finset ℝ := offDiag.image fun e => dist e.1 e.2
  have hmem₀ : (x₀, y₀) ∈ offDiag :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx₀, hy₀⟩, hxy₀⟩
  have hne : Dset.Nonempty := ⟨dist x₀ y₀, Finset.mem_image.mpr ⟨(x₀, y₀), hmem₀, rfl⟩⟩
  have hset : {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y} = (Dset : Set ℝ) := by
    ext r
    simp only [Set.mem_setOf, Finset.mem_coe, Dset, offDiag, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, hx, y, hy, hne', rfl⟩
      exact ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
      exact ⟨x, hx, y, hy, hne', rfl⟩
  have hmin_eq : minDist P = Dset.min' hne := by
    rw [minDist, hset]
    exact IsLeast.csInf_eq (Finset.isLeast_min' Dset hne)
  have hmax_eq : maxDist P = Dset.max' hne := by
    rw [maxDist, hset]
    exact IsGreatest.csSup_eq (Finset.isGreatest_max' Dset hne)
  have hmin_mem : Dset.min' hne ∈ Dset := Finset.min'_mem Dset hne
  obtain ⟨⟨x₁, y₁⟩, hxy₁, hdist₁⟩ := Finset.mem_image.mp hmin_mem
  have hmin_pos : 0 < minDist P := by
    rw [hmin_eq, ← hdist₁]
    exact dist_pos.mpr (Finset.mem_filter.mp hxy₁).2
  have hle : minDist P ≤ maxDist P := by
    rw [hmin_eq, hmax_eq]
    exact Finset.min'_le Dset _ (Finset.max'_mem Dset hne)
  refine ⟨hmin_pos, (one_le_div hmin_pos).mpr hle, ?_⟩
  intro x hx y hy hxy
  have hmem : dist x y ∈ Dset :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩
  rw [hmin_eq, hmax_eq]
  exact ⟨Finset.min'_le Dset _ hmem, Finset.le_max' Dset _ hmem⟩

lemma greedyStep_ne_target {d : ℕ} {E : Finset (Pt d × Pt d)} {t x y : Pt d}
    (hstep : GreedyStep E t x y) : x ≠ t := by
  intro heq
  subst heq
  have hlt : dist y x < dist x x := hstep.2.1
  rw [dist_self] at hlt
  exact not_lt_of_ge dist_nonneg hlt

lemma greedyStep_shrink {d : ℕ} {α : ℝ} {P R : Finset (Pt d)} {E : Finset (Pt d × Pt d)}
    (hG : IsSteinerNavigable α P R E) {t x y : Pt d} (hx : x ∈ P ∪ R) (ht : t ∈ P)
    (hstep : GreedyStep E t x y) :
    y ∈ P ∪ R ∧ dist y t < dist x t / α := by
  have hy : y ∈ P ∪ R := (hG.2.1 x y hstep.1).2
  have hxt : x ≠ t := greedyStep_ne_target hstep
  obtain ⟨v, hvE, hcov⟩ := hG.2.2 x hx t ht hxt.symm
  exact ⟨hy, lt_of_le_of_lt (hstep.2.2 v hvE) hcov⟩

lemma greedyRun_uncons {d : ℕ} {E : Finset (Pt d × Pt d)} {q x₀ : Pt d} :
    ∀ {k : ℕ} {z : Pt d}, GreedyRun E q x₀ (k + 1) z →
      ∃ x₁, GreedyStep E q x₀ x₁ ∧ GreedyRun E q x₁ k z
  | 0, z, GreedyRun.step h0 hstep => by
    cases h0
    exact ⟨z, hstep, GreedyRun.start⟩
  | k + 1, z, GreedyRun.step hrun hstep => by
    obtain ⟨x₁, hfirst, hmid⟩ := greedyRun_uncons hrun
    exact ⟨x₁, hfirst, GreedyRun.step hmid hstep⟩

lemma greedyRun_split {d : ℕ} {E : Finset (Pt d × Pt d)} {q x₀ : Pt d} {m : ℕ} :
    ∀ {n : ℕ} {z : Pt d}, GreedyRun E q x₀ (m + n) z →
      ∃ y, GreedyRun E q x₀ m y ∧ GreedyRun E q y n z
  | 0, z, hrun => ⟨z, hrun, GreedyRun.start⟩
  | n + 1, z, GreedyRun.step hrun hstep => by
    obtain ⟨y, hm, hn⟩ := greedyRun_split hrun
    exact ⟨y, hm, GreedyRun.step hn hstep⟩

lemma greedyRun_dist_lt {d : ℕ} {α : ℝ} (hα : 1 < α) {P R : Finset (Pt d)}
    {E : Finset (Pt d × Pt d)} (hG : IsSteinerNavigable α P R E) {t x₀ : Pt d}
    (hx₀ : x₀ ∈ P ∪ R) (ht : t ∈ P) :
    ∀ {k : ℕ} {x : Pt d}, 1 ≤ k → GreedyRun E t x₀ k x →
      x ∈ P ∪ R ∧ dist x t < dist x₀ t / α ^ k
  | 0, _, hk, _ => absurd hk (by omega)
  | 1, x, _, GreedyRun.step h0 hstep => by
    cases h0
    obtain ⟨hx, hlt⟩ := greedyStep_shrink hG hx₀ ht hstep
    rw [pow_one]
    exact ⟨hx, hlt⟩
  | k + 2, x, _, GreedyRun.step hrun hstep => by
    obtain ⟨hy, hy_lt⟩ := greedyRun_dist_lt hα hG hx₀ ht (by omega) hrun
    obtain ⟨hx, hx_lt⟩ := greedyStep_shrink hG hy ht hstep
    have hα_pos : 0 < α := by linarith
    refine ⟨hx, ?_⟩
    calc dist x t < dist _ t / α := hx_lt
      _ < (dist x₀ t / α ^ (k + 1)) / α := div_lt_div_of_pos_right hy_lt hα_pos
      _ = dist x₀ t / α ^ (k + 2) := by rw [div_div, ← pow_succ]

lemma run_bound_from_P {d : ℕ} {α : ℝ} (hα : 1 < α) {P R : Finset (Pt d)}
    {E : Finset (Pt d × Pt d)} (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E)
    (hN : NoSteinerToSteiner R P E) {t : Pt d} (ht : t ∈ P)
    {x₀ : Pt d} (hx₀ : x₀ ∈ P) {k : ℕ} {x : Pt d} (hrun : GreedyRun E t x₀ k x) :
    k ≤ ⌊Real.logb α (aspectRatio P)⌋₊ + 2 := by
  obtain ⟨hmin_pos, hΔ1, hpair⟩ := dist_bounds P hn
  let j : ℕ := ⌊Real.logb α (aspectRatio P)⌋₊ + 1
  by_contra hk_gt
  have hjk : j + 2 ≤ k := by omega
  have hkeq : k = j + (2 + (k - j - 2)) := by omega
  rw [hkeq] at hrun
  obtain ⟨xj, hrun_j, hrem⟩ := greedyRun_split (m := j) hrun
  have hrem' : GreedyRun E t xj ((1 + (k - j - 2)) + 1) x := by
    have heq2 : 2 + (k - j - 2) = (1 + (k - j - 2)) + 1 := by omega
    rwa [← heq2]
  obtain ⟨xj1, hstep_j, hrem1⟩ := greedyRun_uncons hrem'
  have hrem1' : GreedyRun E t xj1 ((k - j - 2) + 1) x := by
    have heq1 : 1 + (k - j - 2) = (k - j - 2) + 1 := by omega
    rwa [← heq1]
  obtain ⟨_, hstep_j1, _⟩ := greedyRun_uncons hrem1'
  have hxj_ne : xj ≠ t := greedyStep_ne_target hstep_j
  have hxj1_ne : xj1 ≠ t := greedyStep_ne_target hstep_j1
  obtain ⟨_, hfirst, _⟩ := greedyRun_uncons hrun_j
  have hx₀_ne : x₀ ≠ t := greedyStep_ne_target hfirst
  have hx₀_le : dist x₀ t ≤ maxDist P := (hpair x₀ hx₀ t ht hx₀_ne).2
  obtain ⟨hxj_mem, hxj_lt⟩ :=
    greedyRun_dist_lt hα hG (Finset.mem_union_left R hx₀) ht (show 1 ≤ j by omega) hrun_j
  have hα_pos : 0 < α := by linarith
  have hpow_pos : 0 < α ^ j := pow_pos hα_pos j
  have hΔ_pos : 0 < aspectRatio P := by linarith
  have hj_gt : Real.logb α (aspectRatio P) < (j : ℝ) := by
    dsimp [j]
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hΔ_le_pow : aspectRatio P ≤ α ^ j := by
    have hrpow : α ^ (Real.logb α (aspectRatio P)) ≤ α ^ (j : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hα) (le_of_lt hj_gt)
    rwa [Real.rpow_logb hα_pos (ne_of_gt hα) hΔ_pos, Real.rpow_natCast] at hrpow
  have hmax_div_le : maxDist P / α ^ j ≤ minDist P := by
    rw [aspectRatio, div_le_iff₀ hmin_pos] at hΔ_le_pow
    rw [div_le_iff₀ hpow_pos]
    linarith
  have hxj_lt_min : dist xj t < minDist P := by
    calc dist xj t < dist x₀ t / α ^ j := hxj_lt
      _ ≤ maxDist P / α ^ j := div_le_div_of_nonneg_right hx₀_le (le_of_lt hpow_pos)
      _ ≤ minDist P := hmax_div_le
  rcases Finset.mem_union.mp hxj_mem with hxjP | hxjR
  · exact not_lt_of_ge (hpair xj hxjP t ht hxj_ne).1 hxj_lt_min
  · have hxj1P : xj1 ∈ P := hN xj xj1 hstep_j.1 hxjR
    have hxj1_lt : dist xj1 t < minDist P := lt_trans hstep_j.2.1 hxj_lt_min
    exact not_lt_of_ge (hpair xj1 hxj1P t ht hxj1_ne).1 hxj1_lt

end AuxLemma67

theorem solution {d : ℕ} (α : ℝ) (hα : 1 < α) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E) (hN : NoSteinerToSteiner R P E)
    (t : Pt d) (ht : t ∈ P) :
    (∀ x₀ ∈ P, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α (aspectRatio P)⌋₊ + 2) ∧
      (∀ x₀ ∈ R, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α (aspectRatio P)⌋₊ + 3) ∧
      (∀ x₀ ∈ P ∪ R, ∀ k x, GreedyRun E t x₀ k x → GreedyLocalMin E t x → x = t) ∧
      (∀ x₀ ∈ P ∪ R, ∃ k x, GreedyRun E t x₀ k x ∧ GreedyLocalMin E t x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x₀ hx₀ k x hrun
    exact AuxLemma67.run_bound_from_P hα hn hG hN ht hx₀ hrun
  · intro x₀ hx₀ k x hrun
    cases k with
    | zero => omega
    | succ k' =>
      obtain ⟨x₁, hstep₁, hrun₁⟩ := AuxLemma67.greedyRun_uncons hrun
      have hx₁P : x₁ ∈ P := hN x₀ x₁ hstep₁.1 hx₀
      have hk' := AuxLemma67.run_bound_from_P hα hn hG hN ht hx₁P hrun₁
      omega
  · intro x₀ hx₀ k x hrun hloc
    have hx_mem : x ∈ P ∪ R := by
      induction hrun with
      | start => exact hx₀
      | step _ hstep => exact (hG.2.1 _ _ hstep.1).2
    by_contra hxt
    obtain ⟨v, hvE, hcov⟩ := hG.2.2 x hx_mem t ht (Ne.symm hxt)
    unfold Covers at hcov
    have hpos : 0 < dist x t := dist_pos.mpr hxt
    have hlt : dist v t < dist x t := lt_trans hcov (div_lt_self hpos hα)
    exact not_lt_of_ge (hloc v hvE) hlt
  · intro x₀ hx₀
    exact (SteinerNav.descent_terminates (P ∪ R) E hG.2.1 t x₀ hx₀).2
