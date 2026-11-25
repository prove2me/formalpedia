-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:21.183414+00:00
-- url     : https://prove2.me/submissions/199c6f9d-5113-4e95-8d04-a7bf16a2e26d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovSet_nonempty
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_finiteDimensional_of_rank_le
public import Theorems.Thm_SNumbers_ne_top_of_rank_le_of_lt_rank
public import Theorems.Thm_SNumbers_nontrivial_of_natCast_lt_rank
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
private lemma norm_mk_bot (y : Y) :
    ‖((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y))‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · simpa using _root_.Submodule.Quotient.norm_mk_le (S := (⊥ : Submodule 𝕜 Y)) y
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y', hy'_eq, hy'_lt⟩ :=
      Submodule.Quotient.norm_mk_lt
        ((⊥ : Submodule 𝕜 Y).mkQ y : Y ⧸ (⊥ : Submodule 𝕜 Y)) hε
    -- `Submodule.Quotient.mk y' = mkQ y` and `mkQ y' = mkQ y`, so `y' - y ∈ ⊥ = {0}`.
    have h_eq : y' = y := by
      have hker : y' - y ∈ (⊥ : Submodule 𝕜 Y) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hy'_eq]
        change (⊥ : Submodule 𝕜 Y).mkQ y - (⊥ : Submodule 𝕜 Y).mkQ y = 0
        simp
      rwa [Submodule.mem_bot, sub_eq_zero] at hker
    have h_norm_eq : ‖y‖ = ‖y'‖ := by rw [h_eq]
    rw [h_norm_eq]
    exact hy'_lt.le
private lemma deviationFromSubspace_bot (S : X →L[𝕜] Y) :
    deviationFromSubspace S (⊥ : Submodule 𝕜 Y) = ‖S‖ := by
  unfold deviationFromSubspace
  refine le_antisymm ?_ ?_
  · -- `‖(⊥).mkQL ∘ S‖ ≤ ‖S‖`: pointwise `‖[S x]‖ = ‖S x‖ ≤ ‖S‖ * ‖x‖`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [coe_comp, Function.comp_apply, Submodule.mkQL_apply, norm_mk_bot]
    exact S.le_opNorm x
  · -- `‖S‖ ≤ ‖(⊥).mkQL ∘ S‖`: pointwise `‖S x‖ = ‖[S x]‖ ≤ ‖(⊥).mkQL ∘ S‖ * ‖x‖`.
    refine opNorm_le_bound _
      (norm_nonneg ((⊥ : Submodule 𝕜 Y).mkQL.comp S)) fun x => ?_
    rw [← norm_mk_bot (𝕜 := 𝕜) (S x)]
    change ‖((⊥ : Submodule 𝕜 Y).mkQL.comp S) x‖ ≤ _
    exact ((⊥ : Submodule 𝕜 Y).mkQL.comp S).le_opNorm x
variable [CompleteSpace 𝕜]
private lemma one_le_norm_mkQL_of_proper {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {V : Submodule 𝕜 X} [FiniteDimensional 𝕜 V] (hV_ne_top : V ≠ ⊤) :
    (1 : ℝ) ≤ ‖V.mkQL‖ := by
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := by by_contra h; push Not at h; exact hV_ne_top (eq_top_iff.mpr fun x _ => h x)
  -- Limit `r → 1`: enough to show `1 ≤ ‖V.mkQL‖ + ε` for every `ε > 0`. The
  -- `ε ≥ 1` case is trivial (RHS ≥ 0 + 1); for `ε ∈ (0, 1)` we run Riesz at
  -- level `1 − ε`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hε1 : 1 ≤ ε
  · linarith [norm_nonneg V.mkQL]
  have hε1' : ε < 1 := lt_of_not_ge hε1
  have h_aux : (1 - ε : ℝ) < 1 := by linarith
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists h_aux
  have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
  have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
  -- `‖V.mkQL x₀‖ = infDist x₀ V ≥ (1 − ε) · ‖x₀‖` via Riesz.
  have h_quot_ge : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL x₀‖ := by
    have h_norm_eq : ‖V.mkQL x₀‖ = Metric.infDist x₀ V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) x₀
    rw [h_norm_eq, Metric.le_infDist ⟨0, V.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm]
    exact hx₀_dist y hy
  -- `‖V.mkQL‖ · ‖x₀‖ ≥ ‖V.mkQL x₀‖ ≥ (1 − ε) · ‖x₀‖`. Cancel `‖x₀‖ > 0`,
  -- then rearrange.
  have h_op : ‖V.mkQL x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := V.mkQL.le_opNorm x₀
  have h_chain : (1 - ε) * ‖x₀‖ ≤ ‖V.mkQL‖ * ‖x₀‖ := h_quot_ge.trans h_op
  linarith [le_of_mul_le_mul_right h_chain hx₀_norm_pos]
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [CompleteSpace 𝕜]
namespace SNumbers
theorem _root_.solution {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have : Nontrivial X := nontrivial_of_natCast_lt_rank h
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: take `V = ⊥`. `deviation(I, ⊥) = ‖I‖ = 1`.
    have h_rank_bot : Module.rank 𝕜 (⊥ : Submodule 𝕜 X) ≤ (n : Cardinal) := by
      rw [rank_bot]; exact zero_le
    calc kolmogorovNumber I n
        ≤ deviationFromSubspace I ⊥ := kolmogorovNumber_le_deviation h_rank_bot
      _ = ‖I‖ := deviationFromSubspace_bot _
      _ = 1 := norm_id
  · -- `≥ 1`: every admissible `V` is proper, so `‖V.mkQL‖ ≥ 1`, and
    -- `deviation(I, V) = ‖V.mkQL.comp I‖ = ‖V.mkQL‖`.
    refine le_csInf (kolmogorovSet_nonempty I n) ?_
    rintro _ ⟨V, hV, rfl⟩
    have hV_ne_top : V ≠ ⊤ := ne_top_of_rank_le_of_lt_rank hV h
    have : FiniteDimensional 𝕜 V := finiteDimensional_of_rank_le hV
    have h_dev_eq : deviationFromSubspace I V = ‖V.mkQL‖ := by
      show ‖V.mkQL.comp I‖ = ‖V.mkQL‖
      rw [hI_def, ContinuousLinearMap.comp_id]
    rw [h_dev_eq]
    exact one_le_norm_mkQL_of_proper hV_ne_top
end SNumbers
