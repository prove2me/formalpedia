-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.eq_4_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:14:00.243919+00:00
-- url     : https://prove2.me/submissions/754b31fa-43cf-442f-9551-c53e9154e9f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace PDEq49Aux

lemma derivs {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiffOn ℝ 3 F U)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
    HasFDerivAt F (fderiv ℝ F y) y ∧ HasFDerivAt (gradient F) (hess F y) y := by
  have hn : U ∈ nhds y := hU.mem_nhds hy
  refine ⟨((hF.differentiableOn (by norm_num)).differentiableAt hn).hasFDerivAt, ?_⟩
  have h2 : ContDiffOn ℝ 2 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (h2.differentiableOn (by norm_num)).differentiableAt hn
  have hg : DifferentiableAt ℝ (gradient F) y := by
    have : gradient F = fun z => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ F z) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.differentiableAt.comp y hd
  exact hg.hasFDerivAt

end PDEq49Aux

open PDEq49Aux

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hp : p ∈ K)
    (α : ℝ) (hα0 : 0 ≤ α) :
    F (x + α • p) ≤ F x + α * ⟪gradient F x, p⟫_ℝ + α ^ 2 / 2 * (lnorm F x p) ^ 2 := by
  have hC3 : ContDiffOn ℝ 3 F (interior K) := hF.1.1.2.1
  have hpd := hF.1.2.2.2.2 x hx
  -- σ_x(−p) = 0 since p ∈ K
  have hσ0 : sigma K x (-p) = 0 := by
    apply le_antisymm
    · apply csInf_le ⟨0, fun b hb => hb.1⟩
      exact ⟨le_rfl, by simpa using hp⟩
    · exact Real.sInf_nonneg (fun b hb => hb.1)
  have hL : lnorm F x p ^ 2 = ⟪hess F x p, p⟫_ℝ := by
    unfold lnorm
    rw [Real.sq_sqrt]
    by_cases hp0 : p = 0
    · rw [hp0, map_zero, inner_zero_left]
    · exact (hpd p hp0).le
  set L := lnorm F x p ^ 2 with hLdef
  -- Theorem 4.1 with direction −p: F''(x + tp) ⪯ F''(x)
  have h41 : ∀ t ∈ Set.Icc 0 α, x + t • p ∈ interior K ∧
      ⟪hess F (x + t • p) p, p⟫_ℝ ≤ L := by
    intro t ht
    obtain ⟨hmem, hb⟩ := SelfScaledLongStep.PrimalDual.theorem_4_1 K hK F ν hν hF x (-p) hx t ht.1
      (by rw [hσ0, mul_zero]; exact one_pos)
    have e : x - t • -p = x + t • p := by rw [smul_neg, sub_neg_eq_add]
    rw [e] at hmem hb
    refine ⟨hmem, ?_⟩
    have := (hb p).2
    rw [hσ0, mul_zero, sub_zero, one_pow, div_one, one_mul] at this
    rw [hL]; exact this
  have hline : ∀ t ∈ Set.Icc 0 α,
      HasDerivAt (fun s : ℝ => F (x + s • p)) (⟪gradient F (x + t • p), p⟫_ℝ) t ∧
      HasDerivAt (fun s : ℝ => ⟪gradient F (x + s • p), p⟫_ℝ)
        (⟪hess F (x + t • p) p, p⟫_ℝ) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := derivs _ isOpen_interior F hC3 _ (h41 t ht).1
    have hl : HasDerivAt (fun s : ℝ => x + s • p) p t := by
      have := ((hasDerivAt_id t).smul_const p).const_add x
      simpa using this
    refine ⟨?_, ?_⟩
    · refine (h1.comp_hasDerivAt t hl).congr_deriv ?_
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    · refine ((h2.comp_hasDerivAt t hl).inner ℝ (hasDerivAt_const t p)).congr_deriv ?_
      simp
  set g0 := ⟪gradient F x, p⟫_ℝ with hg0
  let k : ℝ → ℝ := fun s => ⟪gradient F (x + s • p), p⟫_ℝ - g0 - s * L
  have hk : ∀ t ∈ Set.Icc 0 α, HasDerivAt k (⟪hess F (x + t • p) p, p⟫_ℝ - L) t := by
    intro t ht
    have h1 := (hline t ht).2
    refine ((h1.sub_const g0).sub (hasDerivAt_mul_const L)).congr_deriv ?_
    ring
  have hk_nonpos : ∀ t ∈ Set.Icc 0 α, k t ≤ 0 := by
    have hanti : AntitoneOn k (Set.Icc 0 α) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 α)
      · intro t ht; exact (hk t ht).continuousAt.continuousWithinAt
      · intro t ht
        exact (hk t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hk t ht').deriv]
        linarith [(h41 t ht').2]
    have h0 : k 0 = 0 := by simp [k, hg0]
    intro t ht
    have := hanti ⟨le_rfl, hα0⟩ ht ht.1
    linarith
  let h : ℝ → ℝ := fun s => F (x + s • p) - F x - s * g0 - s ^ 2 / 2 * L
  have hh : ∀ t ∈ Set.Icc 0 α, HasDerivAt h (k t) t := by
    intro t ht
    have h1 := (hline t ht).1
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * L) (t * L) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).mul_const L
      refine this.congr_deriv ?_
      push_cast; ring
    refine (((h1.sub_const (F x)).sub (hasDerivAt_mul_const g0)).sub hsq).congr_deriv ?_
    simp only [k]
  have hanti : AntitoneOn h (Set.Icc 0 α) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 α)
    · intro t ht; exact (hh t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hh t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hh t (interior_subset ht)).deriv]
      exact hk_nonpos t (interior_subset ht)
  have h0 : h 0 = 0 := by simp [h]
  have := hanti ⟨le_rfl, hα0⟩ ⟨hα0, le_rfl⟩ hα0
  rw [h0] at this
  simp only [h] at this
  linarith
