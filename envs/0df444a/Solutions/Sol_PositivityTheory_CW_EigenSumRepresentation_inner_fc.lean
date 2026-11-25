-- Prove2me | solution 1 for PositivityTheory.CW.EigenSumRepresentation.inner_fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:11.631028+00:00
-- url     : https://prove2.me/submissions/4e95a2d7-a839-4281-adb0-999218700060

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_WordFiltrationCommute
import Theorems.Thm_PositivityTheory_CW_EigenSumRepresentation_inner_basis
import Theorems.Thm_PositivityTheory_CW_EigenSumRepresentation_repr_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenSumRepresentation
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.EigenSumRepresentation
theorem _root_.solution {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (S : Finset ι)
    (hS : ∀ i, i ∉ S → φ (μ i) = 0) (y : V) :
    inner ℂ y (fc b μ φ y) = ∑ i ∈ S, ((φ (μ i) * ‖b.repr y i‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hyU : (b.repr y).support ⊆ (b.repr y).support ∪ S := Finset.subset_union_left
  have hfc : fc b μ φ y = ∑ j ∈ (b.repr y).support ∪ S, b.repr y j • ((φ (μ j) : ℂ) • b j) := by
    conv_lhs => rw [repr_sum (b := b) _ y hyU]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, fc, Module.Basis.constr_basis]
  have key : ∀ j, inner ℂ y (b.repr y j • ((φ (μ j) : ℂ) • b j)) = ((φ (μ j) * ‖b.repr y j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [inner_smul_right, inner_smul_right, ← inner_conj_symm, inner_basis hb]
    push_cast
    rw [← Complex.mul_conj']
    ring
  rw [hfc, inner_sum, Finset.sum_congr rfl (fun j _ => key j)]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro j _ hj
  rw [hS j hj]
  simp
end PositivityTheory.CW.EigenSumRepresentation
