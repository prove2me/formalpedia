-- Prove2me | solution 1 for RossQC.Sufficient.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:58:08.711978+00:00
-- url     : https://prove2.me/submissions/3ce481e7-ce6b-45e4-8458-2fdbefdd36ce

import Mathlib
import Definitions.Def_RossQC_Sufficient_Model

open RossQC.Sufficient Filter Topology

private theorem update_mem (M : Model) (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    {P : ℝ} (hP : P ∈ Set.Icc (0 : ℝ) 1) : M.T P ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [Model.T]
  obtain ⟨hP0, hP1⟩ := hP
  constructor <;> nlinarith [mul_nonneg hπ0 (sub_nonneg.mpr hP1),
    mul_nonneg (sub_nonneg.mpr hπ1) (sub_nonneg.mpr hP1)]

private theorem operator_le (M : Model) (hβ : 0 ≤ M.β)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (f g : ℝ → ℝ)
    (hfg : ∀ P ∈ Set.Icc (0 : ℝ) 1, f P ≤ g P)
    {P : ℝ} (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    min (M.rhs3 f P .produce) (min (M.rhs3 f P .inspect) (M.rhs3 f P .revise)) ≤
      min (M.rhs3 g P .produce) (min (M.rhs3 g P .inspect) (M.rhs3 g P .revise)) := by
  apply min_le_min
  · dsimp [Model.rhs3]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (hfg _ (update_mem M hπ0 hπ1 hP)) hβ) _
  · apply min_le_min
    · dsimp [Model.rhs3]
      have h1 := mul_le_mul_of_nonneg_left (hfg 1 (by simp)) (mul_nonneg hβ hP.1)
      have h2 := mul_le_mul_of_nonneg_left (hfg M.π ⟨hπ0, hπ1⟩)
        (mul_nonneg hβ (sub_nonneg.mpr hP.2))
      linarith
    · dsimp [Model.rhs3]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hfg M.π ⟨hπ0, hπ1⟩) hβ) _

private theorem iter_bounds (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ n P, P ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ M.valueIter n P ∧ M.valueIter n P ≤ M.C / (1 - M.β) := by
  have hden : 0 < 1 - M.β := by linarith
  have hB : 0 ≤ M.C / (1 - M.β) := le_of_lt (div_pos hC0 hden)
  have heq : M.C + M.β * (M.C / (1 - M.β)) = M.C / (1 - M.β) := by
    field_simp
    <;> ring
  intro n
  induction n with
  | zero => intro P hP; exact ⟨le_refl 0, hB⟩
  | succ n ih =>
    intro P hP
    have ht := ih _ (update_mem M hπ0 hπ1 hP)
    have h1 := ih 1 (by simp)
    have hπ := ih M.π ⟨hπ0, hπ1⟩
    have ht0 := ht.1
    have h10 := h1.1
    have hπn := hπ.1
    have hP0 := hP.1
    constructor
    · dsimp [Model.valueIter, Model.rhs3]
      apply le_min
      · positivity
      · apply le_min
        · have hI : 0 ≤ M.I := by linarith
          have hp : 0 ≤ 1 - P := by linarith [hP.2]
          positivity
        · have hR : 0 ≤ M.R := by linarith
          positivity
    · apply le_trans (min_le_left _ _)
      dsimp [Model.rhs3]
      have hc := mul_le_mul_of_nonneg_left hP.2 hC0.le
      have ht' := mul_le_mul_of_nonneg_left ht.2 hβ0.le
      linarith

private theorem iter_time_mono (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) (P : ℝ) (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    Monotone (fun n => M.valueIter n P) := by
  apply monotone_nat_of_le_succ
  have hstep : ∀ n P, P ∈ Set.Icc (0 : ℝ) 1 → M.valueIter n P ≤ M.valueIter (n+1) P := by
    intro n
    induction n with
    | zero => intro P hP; exact (iter_bounds M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR 1 P hP).1
    | succ n ih =>
      intro P hP
      exact operator_le M hβ0.le hπ0 hπ1 _ _ ih hP
  exact fun n => hstep n P hP

private theorem value_tendsto (M : Model) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C)
    (hCI : M.C < M.I) (hIR : M.I < M.R) (P : ℝ) (hP : P ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => M.valueIter n P) atTop (𝓝 (M.value P)) := by
  apply tendsto_nhds_limUnder
  refine ⟨_, tendsto_atTop_ciSup (iter_time_mono M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR P hP) ?_⟩
  refine ⟨M.C / (1 - M.β), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (iter_bounds M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR n P hP).2

private theorem iter_space_mono (M : Model) (hβ0 : 0 < M.β)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1) (hC0 : 0 < M.C) :
    ∀ n, MonotoneOn (M.valueIter n) (Set.Icc (0 : ℝ) 1) := by
  intro n
  induction n with
  | zero => intro P hP Q hQ hPQ; exact le_refl 0
  | succ n ih =>
    intro P hP Q hQ hPQ
    apply min_le_min
    · dsimp [Model.rhs3]
      have ht : M.T P ≤ M.T Q := by
        dsimp [Model.T]
        nlinarith [mul_nonneg (sub_nonneg.mpr hπ1) (sub_nonneg.mpr hPQ)]
      have hv := ih (update_mem M hπ0 hπ1 hP) (update_mem M hπ0 hπ1 hQ) ht
      nlinarith
    · apply min_le_min
      · dsimp [Model.rhs3]
        have hv := ih (show M.π ∈ Set.Icc (0 : ℝ) 1 from ⟨hπ0,hπ1⟩) (by simp) hπ1
        nlinarith [mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.mpr hPQ)) (sub_nonneg.mpr hv)]
      · exact le_refl _

theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    MonotoneOn M.value (Set.Icc (0 : ℝ) 1) := by
  intro P hP Q hQ hPQ
  exact le_of_tendsto_of_tendsto
    (value_tendsto M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR P hP)
    (value_tendsto M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR Q hQ)
    (Filter.Eventually.of_forall (fun n => iter_space_mono M hβ0 hπ0 hπ1 hC0 n hP hQ hPQ))

#print axioms solution
