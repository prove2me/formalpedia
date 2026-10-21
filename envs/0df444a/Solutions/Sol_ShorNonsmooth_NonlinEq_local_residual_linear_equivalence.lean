-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.local_residual_linear_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T13:29:51.614215+00:00
-- url     : https://prove2.me/submissions/719a861c-1f81-4084-91c6-ede35ac09f55

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ η > 0, ∃ a > 0, ∃ M > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ < η →
      a * ‖y‖ ≤ maxResidual ψ y ∧ ∀ i, |ψ i y| ≤ M * ‖y‖ := by
  classical
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, by norm_num, 1, by norm_num, 1, by norm_num, ?_⟩
    intro y hy
    constructor
    · simpa [maxResidual] using
        (Subsingleton.elim y (0 : EuclideanSpace ℝ (Fin 0)))
    · intro i
      exact i.elim0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    let g : Fin n → EuclideanSpace ℝ (Fin n) := fun i => gradient (ψ i) 0
    let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun d i => inner ℝ (g i) d
        map_add' := by intro a b; ext i; simp [inner_add_right]
        map_smul' := by intro c a; ext i; simp [inner_smul_right] }
    have hTinj : Function.Injective T := by
      intro d e hde
      have hsub : T (d - e) = 0 := by simp [map_sub, hde]
      have hcoords : ∀ i, inner ℝ (g i) (d - e) = 0 := by
        intro i
        exact congrFun hsub i
      have horth : d - e ∈ (Submodule.span ℝ (Set.range g))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          rcases hu with ⟨i, rfl⟩
          exact hcoords i
        | zero => simp
        | add a b ha hb iha ihb =>
          simp [inner_add_left, iha, ihb]
        | smul c a ha iha =>
          simp [inner_smul_left, iha]
      have htop : Submodule.span ℝ (Set.range g) = ⊤ := by
        simpa [g] using hind.span_eq_top_of_card_eq_finrank (by simp)
      have hsub0 : d - e = 0 := by
        have := horth
        rw [htop] at this
        simpa using this
      exact sub_eq_zero.mp hsub0
    obtain ⟨K, hKpos, hanti⟩ :=
      (LinearMap.injective_iff_antilipschitz T).mp hTinj
    let Kℝ : ℝ := K
    have hKℝpos : 0 < Kℝ := by exact_mod_cast hKpos
    let ε : ℝ := 1 / (2 * Kℝ)
    have hεpos : 0 < ε := by positivity
    let M₁ : ℝ := 1 + ∑ i, ‖g i‖
    have hM₁pos : 0 < M₁ := by positivity
    have hTnorm : ∀ d, ‖T d‖ ≤ M₁ * ‖d‖ := by
      intro d
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hM₁pos.le (norm_nonneg _))]
      intro i
      calc
        ‖T d i‖ = |inner ℝ (g i) d| := by simp [T]
        _ ≤ ‖g i‖ * ‖d‖ := abs_real_inner_le_norm _ _
        _ ≤ M₁ * ‖d‖ := by
          have hsingle := Finset.single_le_sum
            (fun j hj => norm_nonneg (g j)) (Finset.mem_univ i)
          have hgi : ‖g i‖ ≤ M₁ := by
            dsimp [M₁]
            linarith
          exact mul_le_mul_of_nonneg_right hgi (norm_nonneg _)
    have hsmall : ∀ i, ∀ᶠ y in nhds (0 : EuclideanSpace ℝ (Fin n)),
        ‖ψ i y - fderiv ℝ (ψ i) 0 y‖ ≤ ε * ‖y‖ := by
      intro i
      have hdiff : DifferentiableAt ℝ (ψ i) 0 :=
        ((hψ i).differentiable one_ne_zero) 0
      convert hdiff.hasFDerivAt.isLittleO.def hεpos using 1
      ext y
      simp [h0 i]
    have hsmall_all : ∀ᶠ y in nhds (0 : EuclideanSpace ℝ (Fin n)), ∀ i,
        ‖ψ i y - fderiv ℝ (ψ i) 0 y‖ ≤ ε * ‖y‖ :=
      Filter.eventually_all.mpr hsmall
    rcases Filter.eventually_iff_exists_mem.mp hsmall_all with ⟨V, hV, hVbound⟩
    rcases Metric.mem_nhds_iff.mp hV with ⟨η, hηpos, hηV⟩
    refine ⟨η, hηpos, 1 / (2 * Kℝ), by positivity, M₁ + ε, by positivity, ?_⟩
    intro y hy
    have hyV : y ∈ V := hηV (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
    have hanti0 : ‖y‖ ≤ Kℝ * ‖T y‖ := by
      simpa [Kℝ, dist_eq_norm] using hanti.le_mul_dist y 0
    have hupper_i : ∀ i, |ψ i y| ≤ (M₁ + ε) * ‖y‖ := by
      intro i
      have ht := hVbound y hyV i
      have hf : fderiv ℝ (ψ i) 0 y = inner ℝ (g i) y := by
        simp [g, gradient, InnerProductSpace.toDual_symm_apply]
      calc
        |ψ i y| = |(ψ i y - fderiv ℝ (ψ i) 0 y) + fderiv ℝ (ψ i) 0 y| := by ring_nf
        _ ≤ |ψ i y - fderiv ℝ (ψ i) 0 y| + |fderiv ℝ (ψ i) 0 y| := abs_add_le _ _
        _ ≤ ε * ‖y‖ + M₁ * ‖y‖ := by
          refine add_le_add (by simpa using ht) ?_
          calc
            |fderiv ℝ (ψ i) 0 y| = ‖T y i‖ := by simp [T, hf]
            _ ≤ ‖T y‖ := norm_le_pi_norm (T y) i
            _ ≤ M₁ * ‖y‖ := hTnorm y
        _ = (M₁ + ε) * ‖y‖ := by ring
    have hFupper : maxResidual ψ y ≤ (M₁ + ε) * ‖y‖ := by
      unfold maxResidual
      exact ciSup_le hupper_i
    have hTbound : ‖T y‖ ≤ maxResidual ψ y + ε * ‖y‖ := by
      rw [pi_norm_le_iff_of_nonneg
        (add_nonneg (by unfold maxResidual; exact Real.iSup_nonneg (fun i => abs_nonneg _))
          (mul_nonneg hεpos.le (norm_nonneg _)))]
      intro i
      have ht := hVbound y hyV i
      have hf : fderiv ℝ (ψ i) 0 y = inner ℝ (g i) y := by
        simp [g, gradient, InnerProductSpace.toDual_symm_apply]
      have hcorr : |ψ i y| ≤ maxResidual ψ y := by
        simpa [maxResidual] using Finite.le_ciSup (fun j => |ψ j y|) i
      calc
        ‖T y i‖ = |inner ℝ (g i) y| := by simp [T]
        _ ≤ |ψ i y - fderiv ℝ (ψ i) 0 y| + |ψ i y| := by
          rw [← hf]
          have h := (abs_le.mp (abs_norm_sub_norm_le
            (fderiv ℝ (ψ i) 0 y) (ψ i y))).2
          rw [norm_sub_rev (fderiv ℝ (ψ i) 0 y) (ψ i y)] at h
          simpa [abs_sub_comm] using h
        _ ≤ ε * ‖y‖ + maxResidual ψ y := add_le_add (by simpa using ht) hcorr
        _ = maxResidual ψ y + ε * ‖y‖ := by ring
    have hhalf : ‖y‖ / 2 ≤ Kℝ * maxResidual ψ y := by
      have := hanti0.trans (mul_le_mul_of_nonneg_left hTbound hKℝpos.le)
      have hmul : Kℝ * (maxResidual ψ y + ε * ‖y‖) =
          Kℝ * maxResidual ψ y + ‖y‖ / 2 := by
        simp [ε, hKℝpos.ne']
        field_simp [hKℝpos.ne']
      rw [hmul] at this
      linarith
    constructor
    · have hlow : ‖y‖ ≤ 2 * Kℝ * maxResidual ψ y := by nlinarith
      calc
        (1 / (2 * Kℝ)) * ‖y‖ ≤ (1 / (2 * Kℝ)) * (2 * Kℝ * maxResidual ψ y) := by
          exact mul_le_mul_of_nonneg_left hlow (by positivity)
        _ = maxResidual ψ y := by field_simp [hKℝpos.ne']
    · intro i
      exact hupper_i i
