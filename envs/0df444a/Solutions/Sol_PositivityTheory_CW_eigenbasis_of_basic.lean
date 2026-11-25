-- Prove2me | solution 1 for PositivityTheory.CW.eigenbasis_of_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:22.034547+00:00
-- url     : https://prove2.me/submissions/f9698cb2-348e-4cf8-b7d0-edecd0ec2be7

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenbasisOfBasic
import Theorems.Thm_PositivityTheory_CW_EigenspaceDecomposition_mem_Es
import Theorems.Thm_PositivityTheory_CW_EigenspaceDecomposition_fd

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
open EigenspaceDecomposition
namespace PositivityTheory.CW
theorem _root_.solution : A0 → EigenbasisExists := by
  intro hA n ε V _ _ E h
  obtain ⟨hsym, hnn, -, -⟩ := hA n ε V E h
  haveI : ∀ μ : ℝ, FiniteDimensional ℂ (Es ε E μ) := fun μ => fd h μ
  let f : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) → V :=
    fun i => ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2 : V)
  have hOF : OrthogonalFamily ℂ (fun μ : ℝ => Es ε E μ) (fun μ => (Es ε E μ).subtypeₗᵢ) :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces (T := casimirK ε E) hsym).comp
      (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective
  have hon : Orthonormal ℂ f :=
    hOF.orthonormal_sigma_orthonormal (fun μ => (stdOrthonormalBasis ℂ (Es ε E μ)).orthonormal)
  have hli : LinearIndependent ℂ f := hon.linearIndependent
  have hEs : ∀ μ : ℝ, ∀ v ∈ Es ε E μ, v ∈ Submodule.span ℂ (Set.range f) := by
    intro μ v hv
    have key := (stdOrthonormalBasis ℂ (Es ε E μ)).sum_repr ⟨v, hv⟩
    have hv' : v = ∑ i, ((stdOrthonormalBasis ℂ (Es ε E μ)).repr ⟨v, hv⟩ i) •
        ((stdOrthonormalBasis ℂ (Es ε E μ)) i : V) := by
      have := congrArg Subtype.val key
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [← h.span, Submodule.span_le]
    rintro v ⟨μ, hμ⟩
    exact hEs μ v (mem_Es.mpr hμ)
  have heig : ∀ i, Eig ε E i.1 (f i) := fun i =>
    mem_Es.mp ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2).2
  refine ⟨_, Module.Basis.mk hli hsp, fun i => i.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hon
  · intro i
    simpa using heig i
  · intro i
    refine hnn i.1 (f i) (heig i) ?_
    intro h0
    have := hon.1 i
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · intro R
    haveI := h.fin R
    let W := Submodule.span ℂ {v : V | ∃ μ ≤ R, Eig ε E μ v}
    let g : {i : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) | i.1 ≤ R} → W :=
      fun i => ⟨f i.1, Submodule.subset_span ⟨i.1.1, i.2, heig i.1⟩⟩
    have hg : LinearIndependent ℂ g :=
      LinearIndependent.of_comp W.subtype (hli.comp _ Subtype.val_injective)
    haveI := hg.finite
    exact Set.toFinite _
end PositivityTheory.CW
