-- Prove2me | solution 1 for WorstCaseVaR.KnownMoments.quadratic_form_nonneg_iff_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:22:36.816571+00:00
-- url     : https://prove2.me/submissions/ded58be0-ede5-47ce-b5d3-a68e5cde028f

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open Matrix
open WorstCaseVaR.KnownMoments

theorem solution {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hM : M.IsSymm) :
    (∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ quadFn M ⇑x) ↔ M.PosSemidef := by
  have hherm : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  constructor
  · intro hq
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun y => ?_)
    have hstar : star y = y := by funext p; simp
    rw [hstar]
    obtain ⟨u, hu⟩ : ∃ u : Fin n → ℝ, u = fun i => y (Sum.inl i) := ⟨_, rfl⟩
    have hall : ∀ c : ℝ, c ≠ 0 → 0 ≤ Sum.elim u (fun _ : Fin 1 => c) ⬝ᵥ
        (M *ᵥ Sum.elim u (fun _ : Fin 1 => c)) := by
      intro c hc
      have hscale : Sum.elim u (fun _ : Fin 1 => c) = c • liftVec (c⁻¹ • u) := by
        funext p
        cases p with
        | inl i =>
          simp only [Sum.elim_inl, liftVec, Pi.smul_apply, smul_eq_mul]
          field_simp
        | inr k => simp only [Sum.elim_inr, liftVec, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [hscale, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have h := hq (WithLp.toLp 2 (c⁻¹ • u))
      rw [quadFn] at h
      simp only [WithLp.ofLp_toLp] at h
      nlinarith [mul_nonneg (mul_self_nonneg c) h]
    have hzero : 0 ≤ Sum.elim u (fun _ : Fin 1 => (0:ℝ)) ⬝ᵥ
        (M *ᵥ Sum.elim u (fun _ : Fin 1 => (0:ℝ))) := by
      have hcont : Continuous fun s : ℝ => Sum.elim u (fun _ : Fin 1 => s) ⬝ᵥ
          (M *ᵥ Sum.elim u (fun _ : Fin 1 => s)) := by
        simp only [dotProduct, Matrix.mulVec]
        refine continuous_finset_sum _ fun p _ => ?_
        refine Continuous.mul ?_ (continuous_finset_sum _ fun r _ => ?_)
        · cases p with
          | inl i =>
            simp only [Sum.elim_inl]
            exact continuous_const
          | inr k =>
            simp only [Sum.elim_inr]
            exact continuous_id'
        · refine Continuous.mul continuous_const ?_
          cases r with
          | inl i =>
            simp only [Sum.elim_inl]
            exact continuous_const
          | inr k =>
            simp only [Sum.elim_inr]
            exact continuous_id'
      have hten : Filter.Tendsto (fun s : ℝ => Sum.elim u (fun _ : Fin 1 => s) ⬝ᵥ
          (M *ᵥ Sum.elim u (fun _ : Fin 1 => s)))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (Sum.elim u (fun _ : Fin 1 => (0:ℝ)) ⬝ᵥ
            (M *ᵥ Sum.elim u (fun _ : Fin 1 => (0:ℝ))))) :=
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hten ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hall s (ne_of_gt hs)
    have hy : y = Sum.elim u (fun _ : Fin 1 => y (Sum.inr 0)) := by
      funext p
      cases p with
      | inl i => simp only [Sum.elim_inl, hu]
      | inr k =>
        simp only [Sum.elim_inr]
        rw [Subsingleton.elim k (0 : Fin 1)]
    rw [hy]
    rcases eq_or_ne (y (Sum.inr 0)) 0 with h0 | h0
    · rw [h0]; exact hzero
    · exact hall _ h0
  · intro hpsd x
    have h := hpsd.dotProduct_mulVec_nonneg (liftVec (WithLp.ofLp x))
    have hstar : star (liftVec (WithLp.ofLp x)) = liftVec (WithLp.ofLp x) := by funext p; simp
    rw [hstar] at h
    rw [quadFn]
    exact h
