-- Prove2me | solution 1 for SNumbers.Lifting.kolmogorovNumber_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:58.931052+00:00
-- url     : https://prove2.me/submissions/d75c9803-5655-460c-9c81-311b3e6412df

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_Q_single
public import Theorems.Thm_SNumbers_Lifting_kolmogorovNumber_le_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_finiteDimensional_of_rank_le
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_norm
public import Theorems.Thm_SNumbers_ne_top_of_rank_le_of_lt_rank
public import Theorems.Thm_SNumbers_nontrivial_of_natCast_lt_rank

section
@[expose] public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
namespace SNumbers
namespace Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
section S1a
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma exists_lift_of_pos_norm
    {x : X} (hx : 0 < ‖x‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : 𝕜) (h_in : ‖c⁻¹ • x‖ ≤ 1),
      ‖x‖ < ‖c‖ ∧ ‖c‖ < ‖x‖ + δ ∧
      (Q : BallLp 𝕜 X →L[𝕜] X)
          (letI := Classical.decEq (Ball X);
           lp.single 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c) = x ∧
      (letI := Classical.decEq (Ball X);
       ‖lp.single (E := fun _ : Ball X => 𝕜) 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c‖) = ‖c‖ := by
  obtain ⟨c, hc_lb, hc_ub⟩ :=
    NormedField.exists_lt_norm_lt 𝕜 hx.le (lt_add_of_pos_right _ hδ)
  have hc_pos : 0 < ‖c‖ := hx.trans hc_lb
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc_pos
  have h_in : ‖c⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc_pos, mul_one]; exact hc_lb.le
  refine ⟨c, h_in, hc_lb, hc_ub, ?_, ?_⟩
  · rw [Q_single _ h_in c, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
  · let := Classical.decEq (Ball X)
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
end S1a
section S3
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end S3
section S5
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
private lemma one_le_norm_Q_sub_L (n : ℕ) (h_dim : (n : Cardinal) < Module.rank 𝕜 X)
    (L : BallLp 𝕜 X →L[𝕜] X) (hL : L.rank ≤ (n : Cardinal)) :
    1 ≤ ‖(Q : BallLp 𝕜 X →L[𝕜] X) - L‖ := by
  set V : Submodule 𝕜 X := LinearMap.range (L : BallLp 𝕜 X →ₗ[𝕜] X)
  have : FiniteDimensional 𝕜 V := finiteDimensional_of_rank_le hL
  have hV_ne_top : V ≠ ⊤ := ne_top_of_rank_le_of_lt_rank hL h_dim
  have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hV_exists : ∃ x : X, x ∉ V := by by_contra h; push Not at h; exact hV_ne_top (eq_top_iff.mpr fun x _ => h x)
  -- Limit `r → 1`: enough to show `1 ≤ ‖Q − L‖ + ε` for every `ε > 0`. The
  -- `ε ≥ 1` case is trivial; for `ε ∈ (0, 1)` we run Riesz at level `1 − ε/2`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hε1 : 1 ≤ ε
  · linarith [norm_nonneg ((Q : BallLp 𝕜 X →L[𝕜] X) - L)]
  have hε1' : ε < 1 := lt_of_not_ge hε1
  have h1ε_pos : (0 : ℝ) < 1 - ε := by linarith
  -- Riesz at level `1 − ε/2`.
  obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ :=
    riesz_lemma hV_closed hV_exists (by linarith : (1 - ε / 2 : ℝ) < 1)
  have hx₀_pos : 0 < ‖x₀‖ :=
    norm_pos_iff.mpr (fun h => hx₀_ne (h ▸ V.zero_mem))
  -- Pick `c` with `‖x₀‖ < ‖c‖ < ‖x₀‖ + δ`, `δ := ε·‖x₀‖/(2(1−ε))`.
  set δ : ℝ := ε * ‖x₀‖ / (2 * (1 - ε)) with hδ_def
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨c, _, hc_lb, hc_ub, hα_Q, hα_norm⟩ :=
    exists_lift_of_pos_norm (𝕜 := 𝕜) hx₀_pos hδ_pos
  let := Classical.decEq (Ball X)
  set α : BallLp 𝕜 X := lp.single 1 (⟨c⁻¹ • x₀, _⟩ : Ball X) c
  -- `(1 − ε/2) · ‖x₀‖ ≤ ‖x₀ − L α‖ = ‖(Q − L) α‖ ≤ ‖Q − L‖ · ‖c‖`.
  have h_riesz : (1 - ε / 2) * ‖x₀‖ ≤ ‖x₀ - L α‖ :=
    hx₀_dist (L α) ⟨α, rfl⟩
  have h_op := ((Q : BallLp 𝕜 X →L[𝕜] X) - L).le_opNorm α
  rw [sub_apply, hα_Q, hα_norm] at h_op
  have h_chain := h_riesz.trans h_op
  -- The choice of `δ` ensures `(1 − ε) · ‖c‖ < (1 − ε/2) · ‖x₀‖`.
  have h_lhs : (1 - ε) * ‖c‖ < (1 - ε / 2) * ‖x₀‖ := by
    calc (1 - ε) * ‖c‖
        < (1 - ε) * (‖x₀‖ + δ) := mul_lt_mul_of_pos_left hc_ub h1ε_pos
      _ = (1 - ε) * ‖x₀‖ + ε * ‖x₀‖ / 2 := by rw [hδ_def]; field_simp
      _ = (1 - ε / 2) * ‖x₀‖ := by ring
  -- `(1 - ε) · ‖c‖ < ‖Q − L‖ · ‖c‖`, cancel `‖c‖ > 0` to get `1 - ε ≤ ‖Q − L‖`,
  -- then rearrange to `1 ≤ ‖Q − L‖ + ε`.
  have : (1 - ε : ℝ) ≤ ‖(Q : BallLp 𝕜 X →L[𝕜] X) - L‖ :=
    (lt_of_mul_lt_mul_right (h_lhs.trans_le h_chain) (norm_nonneg _)).le
  linarith
end S5
section S5b
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
end S5b
section Pietsch
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Pietsch
end Lifting
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
namespace SNumbers.Lifting
theorem _root_.solution (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    kolmogorovNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  have : Nontrivial X := nontrivial_of_natCast_lt_rank h
  refine le_antisymm ((kolmogorovNumber_le_norm _ _).trans norm_id.le) ?_
  show 1 ≤ approximationNumber
    ((ContinuousLinearMap.id 𝕜 X).comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
  rw [ContinuousLinearMap.id_comp]
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro _ ⟨L, hL_rank, rfl⟩
  exact one_le_norm_Q_sub_L n h L hL_rank
end SNumbers.Lifting
