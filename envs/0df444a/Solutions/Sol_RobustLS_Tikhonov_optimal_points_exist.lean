-- Prove2me | solution 1 for RobustLS.Tikhonov.optimal_points_exist
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:28:09.346474+00:00
-- url     : https://prove2.me/submissions/79c9c53d-1de9-4fcf-a0e8-710e55539239

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

lemma aux_rlt_abs_le_eucNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ eucNorm v := by
  unfold eucNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j))
    (Finset.mem_univ i)

lemma aux_rlt_eucNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v :=
  Real.sqrt_nonneg _

lemma aux_rlt_continuous_eucNorm {ι : Type*} [Fintype ι] :
    Continuous (fun v : ι → ℝ => eucNorm v) := by
  unfold eucNorm
  fun_prop

lemma aux_rlt_continuous_stackOne {m : ℕ} : Continuous (fun x : Fin m → ℝ => stackOne x) := by
  apply continuous_pi
  intro j
  cases j with
  | inl i => simp only [stackOne, Sum.elim_inl]; exact continuous_apply i
  | inr u => simp only [stackOne, Sum.elim_inr]; exact continuous_const

lemma aux_rlt_norm_le_stackOne {m : ℕ} (x : Fin m → ℝ) : ‖x‖ ≤ eucNorm (stackOne x) := by
  refine (pi_norm_le_iff_of_nonneg (aux_rlt_eucNorm_nonneg _)).2 ?_
  intro i
  rw [Real.norm_eq_abs]
  have := aux_rlt_abs_le_eucNorm (stackOne x) (Sum.inl i)
  simpa [stackOne] using this

lemma aux_rlt_primal {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    ∃ (x : Fin m → ℝ) (lam tau : ℝ), IsSOCPOptimal A b x lam tau := by
  set f : (Fin m → ℝ) → ℝ := fun x => eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) with hf
  have hcont : Continuous f := by
    have h1 : Continuous (fun x : Fin m → ℝ => A *ᵥ x - b) := by
      exact (Continuous.matrix_mulVec continuous_const continuous_id).sub continuous_const
    exact (aux_rlt_continuous_eucNorm.comp h1).add
      (aux_rlt_continuous_eucNorm.comp aux_rlt_continuous_stackOne)
  have htend : Filter.Tendsto f (Filter.cocompact (Fin m → ℝ)) Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun x => ?_) tendsto_norm_cocompact_atTop
    have h1 := aux_rlt_norm_le_stackOne x
    have h2 := aux_rlt_eucNorm_nonneg (A *ᵥ x - b)
    simp only [hf]
    linarith
  obtain ⟨x0, hx0⟩ := hcont.exists_forall_le htend
  refine ⟨x0, f x0, eucNorm (stackOne x0), ⟨?_, le_refl _⟩, ?_⟩
  · simp only [hf]; linarith
  · intro x' lam' tau' ⟨h1, h2⟩
    have := hx0 x'
    simp only [hf] at this ⊢
    linarith

lemma aux_rlt_dual {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    ∃ (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ), IsDualOptimal A b z u v := by
  set S : Set ((Fin n → ℝ) × (Fin m → ℝ) × ℝ) :=
    {p | IsDualFeasible A p.1 p.2.1 p.2.2} with hS
  have hclosed : IsClosed S := by
    have hc1 : IsClosed {p : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | Aᵀ *ᵥ p.1 + p.2.1 = 0} := by
      apply isClosed_eq _ continuous_const
      exact (Continuous.matrix_mulVec continuous_const continuous_fst).add
        (continuous_fst.comp continuous_snd)
    have hc2 : IsClosed {p : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | eucNorm p.1 ≤ 1} :=
      isClosed_le (aux_rlt_continuous_eucNorm.comp continuous_fst) continuous_const
    have hc3 : IsClosed
        {p : (Fin n → ℝ) × (Fin m → ℝ) × ℝ | eucNorm (stackScalar p.2.1 p.2.2) ≤ 1} := by
      apply isClosed_le _ continuous_const
      apply aux_rlt_continuous_eucNorm.comp
      apply continuous_pi
      intro j
      cases j with
      | inl i =>
        simp only [stackScalar, Sum.elim_inl]
        exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
      | inr u =>
        simp only [stackScalar, Sum.elim_inr]
        exact continuous_snd.comp continuous_snd
    exact hc1.inter (hc2.inter hc3)
  have hsub : S ⊆ Metric.closedBall 0 1 := by
    rintro ⟨z, u, v⟩ ⟨_, hz, huv⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => ?_)
      rw [Real.norm_eq_abs]
      exact (aux_rlt_abs_le_eucNorm z i).trans hz
    · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => ?_)
      rw [Real.norm_eq_abs]
      have := (aux_rlt_abs_le_eucNorm (stackScalar u v) (Sum.inl i)).trans huv
      simpa [stackScalar] using this
    · show ‖v‖ ≤ 1
      rw [Real.norm_eq_abs]
      have := (aux_rlt_abs_le_eucNorm (stackScalar u v) (Sum.inr ())).trans huv
      simpa [stackScalar] using this
  have hcompact : IsCompact S := (isCompact_closedBall 0 1).of_isClosed_subset hclosed hsub
  have hne : S.Nonempty := by
    refine ⟨(0, 0, 0), ?_, ?_, ?_⟩
    · simp
    · simp [eucNorm]
    · have : stackScalar (0 : Fin m → ℝ) (0 : ℝ) = 0 := by
        funext j
        cases j <;> simp [stackScalar]
      simp only
      rw [this]
      simp [eucNorm]
  set g : (Fin n → ℝ) × (Fin m → ℝ) × ℝ → ℝ := fun p => dualObjective b p.1 p.2.2 with hg
  have hgc : Continuous g := by
    simp only [hg, dualObjective, dotProduct]
    fun_prop
  obtain ⟨⟨z, u, v⟩, hmem, hmax⟩ := hcompact.exists_isMaxOn hne hgc.continuousOn
  refine ⟨z, u, v, hmem, ?_⟩
  intro z' u' v' h'
  have := hmax (show (z', u', v') ∈ S from h')
  simpa [hg] using this

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    (∃ (x : Fin m → ℝ) (lam tau : ℝ), IsSOCPOptimal A b x lam tau) ∧
      (∃ (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ), IsDualOptimal A b z u v) :=
  ⟨aux_rlt_primal A b, aux_rlt_dual A b⟩
