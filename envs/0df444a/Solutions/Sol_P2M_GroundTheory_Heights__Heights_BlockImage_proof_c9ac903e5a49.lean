-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockImage_proof_c9ac903e5a49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:23.682627+00:00
-- url     : https://prove2.me/submissions/8fbb588a-3ebf-4e61-8348-0dfbfaa73c7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_algebraMap_injective_1149ee63111d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open BlockImage
namespace GroundTheory.Heights₂.Heights
namespace BlockImage
theorem _root_.solution (hDim : IntDomainDim.Statement) (hTr : ConeTrdeg.Statement) :
    BlockImage.Statement := by
  refine ⟨fun ι _ _ n P k₀ ↦ ⟨projVariety P k₀, rfl⟩, ?_⟩
  intro ι _ _ n Ω _ y k₀ D hA
  refine ⟨comap_mCoordIdeal y k₀, fun hB ↦ ?_⟩
  obtain ⟨-, hMP, hHor, hKd⟩ := hA
  rw [← comap_mCoordIdeal y k₀]
  have hMP' : Geo.IsMultiProjPrime (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP ⊢
    refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename
      (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀)
      (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) ?_ hMP
    rintro ⟨k, i⟩ ⟨u, hu⟩
    obtain rfl : k₀ = k := hu
    exact ⟨⟨(), i⟩, rfl⟩
  have hHor' : Geo.IsHorizontal (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor
    simp only [Ideal.mem_comap]
    rw [rename_C]
  refine ⟨inferInstance, hMP', hHor', ?_⟩

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hMP.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    simp [Geo.mConeMap, h0]
  rw [comap_mCoordIdeal y k₀] at hHor' hMP' ⊢
  have := hMP.1
  have := hMP'.1
  have dimA := hDim _ (algebraMap_injective _ hHor)
  have dimA' := hDim _ (algebraMap_injective _ hHor')
  rw [hTr ι (blockIdx n) Ω y (birational_of_block y k₀ hB) hrel hHor] at dimA
  rw [hTr Unit (blockIdx fun _ : Unit ↦ n k₀) Ω _ hB (fun _ ↦ hrel k₀) hHor'] at dimA'
  rw [hKd] at dimA
  have h1 : ((D + 1 + Fintype.card ι : ℕ) : ℕ∞) =
      (Algebra.trdeg ℤ Ω + Fintype.card ι).toENat + 1 := by exact_mod_cast dimA
  simp only [map_add, map_natCast] at h1
  have key : (Algebra.trdeg ℤ Ω).toENat = D := by
    generalize (Algebra.trdeg ℤ Ω).toENat = t at h1 ⊢
    induction t using ENat.recTopCoe with
    | top => simp at h1
    | coe m =>
      norm_cast at h1 ⊢
      omega
  rw [dimA']
  simp only [map_add, map_natCast, Fintype.card_unit, key]
  norm_cast
end BlockImage
end GroundTheory.Heights₂.Heights
