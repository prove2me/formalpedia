-- Prove2me | solution 1 for ParamSDO.Transition.transition_iff_frontier
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:28:10.840154+00:00
-- url     : https://prove2.me/submissions/d6f35296-3edc-442d-b56f-a4b7ab868a06

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting
import Theorems.Thm_ParamSDO_Transition_strong_duality
import Theorems.Thm_ParamSDO_Transition_ranks_maximal
import Theorems.Thm_ParamSDO_Transition_optimality_conditions_1

open ParamSDO.Transition Matrix

lemma psdo_pair_lin {n : ℕ} (M X Y : Matrix (Fin n) (Fin n) ℝ) (a c : ℝ) :
    pair M (a • X + c • Y) = a * pair M X + c * pair M Y := by
  unfold pair
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

lemma psdo_Pstar_convex {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : Convex ℝ (Pstar A b C Cbar ϵ) := by
  intro X hX Y hY a c ha hc hac
  have hval : pair (C + ϵ • Cbar) Y = pair (C + ϵ • Cbar) X := by
    have := hY.2.trans hX.2.symm; exact_mod_cast this
  refine ⟨⟨(hX.1.1.smul ha).add (hY.1.1.smul hc), fun i => ?_⟩, ?_⟩
  · rw [psdo_pair_lin, hX.1.2 i, hY.1.2 i, ← add_mul, hac, one_mul]
  · rw [psdo_pair_lin, hval, ← add_mul, hac, one_mul]; exact hX.2

lemma psdo_Dstar_convex {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : Convex ℝ (Dstar A b C Cbar ϵ) := by
  rintro ⟨y, S⟩ hp ⟨y', S'⟩ hq a c ha hc hac
  have hval : b ⬝ᵥ y' = b ⬝ᵥ y := by
    have := hq.2.trans hp.2.symm; exact_mod_cast this
  refine ⟨⟨?_, (hp.1.2.smul ha).add (hq.1.2.smul hc)⟩, ?_⟩
  · have e1 := hp.1.1
    have e2 := hq.1.1
    simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    calc ∑ i, (a * y i + c * y' i) • A i + (a • S + c • S')
        = a • (∑ i, y i • A i + S) + c • (∑ i, y' i • A i + S') := by
          simp only [add_smul, mul_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
          abel
      _ = C + ϵ • Cbar := by rw [e1, e2, ← add_smul, hac, one_smul]
  · simp only [Prod.smul_mk, Prod.mk_add_mk, dotProduct_add, dotProduct_smul, smul_eq_mul, hval]
    rw [← add_mul, hac, one_mul]; exact hp.2

lemma psdo_ri_nonempty_P {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (h : (Pstar A b C Cbar ϵ).Nonempty) :
    (intrinsicInterior ℝ (Pstar A b C Cbar ϵ)).Nonempty := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedSpace
  exact Set.Nonempty.intrinsicInterior (psdo_Pstar_convex A b C Cbar ϵ) h

lemma psdo_ri_nonempty_D {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) (h : (Dstar A b C Cbar ϵ).Nonempty) :
    (intrinsicInterior ℝ (Dstar A b C Cbar ϵ)).Nonempty := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedSpace
  exact Set.Nonempty.intrinsicInterior (psdo_Dstar_convex A b C Cbar ϵ) h

lemma psdo_rank_add_le {n : ℕ} {X S : Matrix (Fin n) (Fin n) ℝ} (h : X * S = 0) :
    X.rank + S.rank ≤ n := by
  have hk : LinearMap.range S.mulVecLin ≤ LinearMap.ker X.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h,
      Matrix.zero_mulVec]
  have e1 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  have := Submodule.finrank_mono hk
  unfold Matrix.rank
  simp only [Module.finrank_fin_fun] at e1
  omega

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵbar : ℝ, IsTransitionPoint A b C Cbar ϵbar ↔
      ∃ θ σ : ℕ, θ + σ ≤ n ∧
        ϵbar ∈ frontier (Srank A b C Cbar θ σ) ∩ interior (domE A b C Cbar) := by
  set U := interior (domE A b C Cbar) with hU
  have hUo : IsOpen U := isOpen_interior
  -- membership in `Srank` is determined by the ranks
  have key : ∀ ϵ ∈ U, ∀ θ σ : ℕ,
      ϵ ∈ Srank A b C Cbar θ σ ↔ (rkX A b C Cbar ϵ = θ ∧ rkS A b C Cbar ϵ = σ) := by
    intro ϵ hϵ θ σ
    obtain ⟨hPn, -, hDn, -⟩ := strong_duality A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
    have hrm := ranks_maximal A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
    constructor
    · rintro ⟨⟨X, p, hXp, hX, hp⟩, -⟩
      rw [intrinsicInterior_prod_eq] at hXp
      exact ⟨(hrm.1 X hXp.1).2 ▸ hX, (hrm.2 p hXp.2).2 ▸ hp⟩
    · rintro ⟨rfl, rfl⟩
      obtain ⟨X, hX⟩ := psdo_ri_nonempty_P A b C Cbar ϵ hPn
      obtain ⟨p, hp⟩ := psdo_ri_nonempty_D A b C Cbar ϵ hDn
      refine ⟨⟨X, p, ?_, (hrm.1 X hX).2, (hrm.2 p hp).2⟩, hϵ⟩
      rw [intrinsicInterior_prod_eq]; exact ⟨hX, hp⟩
  have hsum : ∀ ϵ ∈ U, rkX A b C Cbar ϵ + rkS A b C Cbar ϵ ≤ n := by
    intro ϵ hϵ
    obtain ⟨hPn, -, hDn, -⟩ := strong_duality A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
    have hrm := ranks_maximal A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
    obtain ⟨X, hX⟩ := psdo_ri_nonempty_P A b C Cbar ϵ hPn
    obtain ⟨⟨y, S⟩, hp⟩ := psdo_ri_nonempty_D A b C Cbar ϵ hDn
    have hXS := ((optimality_conditions_1 A b C Cbar hA hC hCbar h1 h2 ϵ hϵ X y S).1
      ⟨intrinsicInterior_subset hX, intrinsicInterior_subset hp⟩).2.2
    rw [← (hrm.1 X hX).2, ← (hrm.2 _ hp).2]
    exact psdo_rank_add_le hXS
  intro ϵbar
  constructor
  · rintro ⟨hϵU, htr⟩
    refine ⟨_, _, hsum ϵbar hϵU, ⟨?_, ?_⟩, hϵU⟩
    · exact subset_closure ((key ϵbar hϵU _ _).2 ⟨rfl, rfl⟩)
    · intro hint
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
      obtain ⟨ϵ, ⟨hϵI, hϵU'⟩, hne⟩ := htr δ hδ
      rw [← Real.ball_eq_Ioo] at hϵI
      have := (key ϵ hϵU' _ _).1 (hball hϵI)
      tauto
  · rintro ⟨θ, σ, -, hfr, hϵU⟩
    refine ⟨hϵU, fun δ hδ => ?_⟩
    obtain ⟨δ', hδ', hball'⟩ := Metric.isOpen_iff.1 hUo ϵbar hϵU
    by_cases hin : ϵbar ∈ Srank A b C Cbar θ σ
    · obtain ⟨hθ, hσ⟩ := (key ϵbar hϵU _ _).1 hin
      have hnot : ¬ Metric.ball ϵbar (min δ δ') ⊆ Srank A b C Cbar θ σ := by
        intro hsub
        exact hfr.2 (mem_interior_iff_mem_nhds.2
          (Metric.mem_nhds_iff.2 ⟨_, lt_min hδ hδ', hsub⟩))
      obtain ⟨ϵ, hϵb, hϵS⟩ := Set.not_subset.1 hnot
      have hϵU' : ϵ ∈ U := hball' (Metric.ball_subset_ball (min_le_right _ _) hϵb)
      have hϵI : ϵ ∈ Set.Ioo (ϵbar - δ) (ϵbar + δ) := by
        rw [← Real.ball_eq_Ioo]; exact Metric.ball_subset_ball (min_le_left _ _) hϵb
      refine ⟨ϵ, ⟨hϵI, hϵU'⟩, ?_⟩
      rw [key ϵ hϵU'] at hϵS
      subst hθ hσ
      tauto
    · have hne : ¬ (rkX A b C Cbar ϵbar = θ ∧ rkS A b C Cbar ϵbar = σ) :=
        fun h => hin ((key ϵbar hϵU _ _).2 h)
      obtain ⟨ϵ, hϵS, hd⟩ := Metric.mem_closure_iff.1 hfr.1 δ hδ
      have hϵU' : ϵ ∈ U := hϵS.2
      obtain ⟨hθ, hσ⟩ := (key ϵ hϵU' _ _).1 hϵS
      refine ⟨ϵ, ⟨?_, hϵU'⟩, ?_⟩
      · rw [← Real.ball_eq_Ioo, Metric.mem_ball, dist_comm]; exact hd
      · subst hθ hσ; tauto
