-- Prove2me | solution 1 for SNumbers.gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:47:13.283825+00:00
-- url     : https://prove2.me/submissions/d2d55680-1261-454f-b5a2-c349a61e8986

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_sum_le_sqrt_card_mul_sqrt_sum_sq
public import Theorems.Thm_SNumbers_exists_triangular_system_hilbert
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
namespace SNumbers
theorem _root_.solution
    (S : X →L[𝕜] H) (n : ℕ) :
    gelfandNumber S n ≤ Real.sqrt ((n : ℝ) + 1) * bernsteinNumber S n := by
  have hb : 0 ≤ bernsteinNumber S n := bernsteinNumber_nonneg S n
  have hfacs : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  by_contra h
  rw [not_le] at h
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between h
  have hγpos : 0 < γ := lt_of_le_of_lt (by positivity) hγ1
  obtain ⟨e, hSe, hen, hortho⟩ := exists_triangular_system_hilbert S hγpos hγ2 (n + 1) le_rfl
  have hon : Orthonormal 𝕜 (fun j => S (e j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · rw [hortho i j hlt]; simp [ne_of_lt hlt]
    · subst heq; rw [inner_self_eq_norm_sq_to_K, hSe i]; simp
    · rw [← inner_conj_symm, hortho j i hgt]; simp [ne_of_gt hgt]
  have hSx : ∀ g : Fin (n + 1) → 𝕜, S (∑ i, g i • e i) = ∑ i, g i • S (e i) := by
    intro g; rw [map_sum]; simp_rw [map_smul]
  have hgj : ∀ (g : Fin (n + 1) → 𝕜) (j), inner 𝕜 (S (e j)) (S (∑ i, g i • e i)) = g j := by
    intro g j
    rw [hSx g, inner_sum,
      Finset.sum_eq_single j
        (fun i _ hij => by
          rw [inner_smul_right, (orthonormal_iff_ite (𝕜 := 𝕜)).mp hon j i,
            if_neg (Ne.symm hij), mul_zero])
        (fun hj => absurd (Finset.mem_univ j) hj)]
    rw [inner_smul_right, (orthonormal_iff_ite (𝕜 := 𝕜)).mp hon j j, if_pos rfl, mul_one]
  have hindep : LinearIndependent 𝕜 e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := hgj g j
    rw [hg, map_zero, inner_zero_right] at hj
    exact hj.symm
  set M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range e) with hM
  have hrankM : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal) := by
    classical
    have : Fintype (Set.range e) := Set.fintypeRange e
    rw [hM, rank_span hindep, Cardinal.mk_fintype,
      Set.card_range_of_injective hindep.injective, Fintype.card_fin]
  have hgain : γ / Real.sqrt ((n : ℝ) + 1) ≤ gainOnSubspace S M := by
    refine le_gainOnSubspace ?_ ?_
    · intro hbot
      have he0 : e 0 ∈ M := Submodule.subset_span ⟨0, rfl⟩
      rw [hbot, Submodule.mem_bot] at he0
      have h0 : ‖S (e 0)‖ = 0 := by rw [he0, map_zero, norm_zero]
      rw [hSe 0] at h0; norm_num at h0
    · intro x hxM hxne
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hxM
      have hxpos : 0 < ‖∑ i, g i • e i‖ := norm_pos_iff.mpr hxne
      have hpars : ∑ j, ‖g j‖ ^ 2 = ‖S (∑ i, g i • e i)‖ ^ 2 := by
        have hK : (∑ j, ‖g j‖ ^ 2 : 𝕜) = (‖S (∑ i, g i • e i)‖ ^ 2 : 𝕜) := by
          rw [← inner_self_eq_norm_sq_to_K]
          nth_rewrite 1 [hSx g]
          rw [sum_inner]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [inner_smul_left, hgj g i, RCLike.conj_mul]
        exact_mod_cast hK
      have hsum_abs : ∑ j, ‖g j‖ ≤ Real.sqrt ((n : ℝ) + 1) * ‖S (∑ i, g i • e i)‖ := by
        refine (SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq fun j => ‖g j‖).trans ?_
        rw [hpars, Real.sqrt_sq (norm_nonneg _), Fintype.card_fin]
        push_cast
        rfl
      have hnormx : ‖∑ i, g i • e i‖ ≤ Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖ := by
        calc ‖∑ i, g i • e i‖
            ≤ ∑ i, ‖g i • e i‖ := norm_sum_le _ _
          _ = ∑ i, ‖g i‖ * ‖e i‖ := by simp_rw [norm_smul]
          _ ≤ ∑ i, ‖g i‖ * (1 / γ) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hen i) (norm_nonneg _)
          _ = (∑ i, ‖g i‖) * (1 / γ) := by rw [← Finset.sum_mul]
          _ ≤ Real.sqrt ((n : ℝ) + 1) * ‖S (∑ i, g i • e i)‖ * (1 / γ) :=
              mul_le_mul_of_nonneg_right hsum_abs (by positivity)
          _ = Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖ := by ring
      rw [le_div_iff₀ hxpos]
      calc γ / Real.sqrt ((n : ℝ) + 1) * ‖∑ i, g i • e i‖
          ≤ γ / Real.sqrt ((n : ℝ) + 1) *
              (Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖) :=
            mul_le_mul_of_nonneg_left hnormx (by positivity)
        _ = ‖S (∑ i, g i • e i)‖ := by field_simp
  have hble : gainOnSubspace S M ≤ bernsteinNumber S n :=
    le_csSup (bddAbove_bernsteinSet S n) ⟨M, hrankM, rfl⟩
  have hfin : γ / Real.sqrt ((n : ℝ) + 1) ≤ bernsteinNumber S n := le_trans hgain hble
  rw [div_le_iff₀ hfacs] at hfin
  nlinarith [hγ1, hfin]
end SNumbers
