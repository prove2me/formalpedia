-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ballFiniteVG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:08.859098+00:00
-- url     : https://prove2.me/submissions/a4c0868c-698d-45c1-af8e-85c459791d1c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_contVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_entry_leVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
private lemma Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
section supnorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end supnorm
section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
end frob
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (R : ℝ) :
    ν {g | hs (toM g) ≤ R} < ⊤ := by
  classical
  have hJ := Jm_mul_self_eq_one' ε
  let K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | inUJ ε M ∧ hs M ≤ R}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
          continuous_id) continuous_const
      · exact isClosed_le hs_contVG continuous_const
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨max 1 R, fun M hM => ?_⟩
      rw [Matrix.norm_le_iff (le_trans zero_le_one (le_max_left _ _))]
      intro i j
      have h1 := le_trans (hs_entry_leVG M i j) hM.2
      have h0 := norm_nonneg (M i j)
      by_cases hc : ‖M i j‖ ≤ 1
      · exact le_trans hc (le_max_left _ _)
      · push_neg at hc
        have : ‖M i j‖ ≤ ‖M i j‖ ^ 2 := by nlinarith
        exact le_trans (le_trans this h1) (le_max_right _ _)
  let e : UJ ε → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun g => Units.embedProduct _ (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have he : Topology.IsInducing e :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  let ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))
  have hψ : Continuous ψ :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hinv : ∀ M : Matrix (Fin n) (Fin n) ℂ, inUJ ε M →
      (Jm ε * Mᴴ * Jm ε) * M = 1 ∧ M * (Jm ε * Mᴴ * Jm ε) = 1 := by
    intro M hM
    have hM' : Mᴴ * Jm ε * M = Jm ε := hM
    have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', hJ]
    exact ⟨h1, mul_eq_one_comm.mp h1⟩
  have himg : e '' {g | hs (toM g) ≤ R} = ψ '' K := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨toM g, ⟨g.2, hg⟩, ?_⟩
      have hinvg : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) = Jm ε * (toM g)ᴴ * Jm ε :=
        Units.inv_eq_of_mul_eq_one_right (hinv (toM g) g.2).2
      simp only [ψ, e, Units.embedProduct_apply, hinvg]
    · rintro ⟨M, ⟨hM, hR⟩, rfl⟩
      let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Jm ε * Mᴴ * Jm ε, (hinv M hM).2, (hinv M hM).1⟩
      refine ⟨⟨u, hM⟩, hR, ?_⟩
      simp only [ψ, e, Units.embedProduct_apply]
      rfl
  have hS : IsCompact {g : UJ ε | hs (toM g) ≤ R} := by
    rw [he.isCompact_iff, himg]
    exact hKc.image hψ
  exact hS.measure_lt_top
end ReciprocityTheory.ChartRestriction.DS.S7
