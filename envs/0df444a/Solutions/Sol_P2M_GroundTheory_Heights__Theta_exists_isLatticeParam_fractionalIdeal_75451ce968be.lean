-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:47.948798+00:00
-- url     : https://prove2.me/submissions/f0bade80-5c8d-4216-ac82-a0290ece2a71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ τ : ℍ, IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by
  set b := basisOfFractionalIdeal K I
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b]
  let e : Module.Free.ChooseBasisIndex ℤ I ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  set ω₀ := b (e.symm 0)
  set ω₁ := b (e.symm 1)
  have hrange : Set.range b = {ω₀, ω₁} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      fin_cases j
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have hI : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({ω₀, ω₁} : Set K) : Set K) := by
    rw [← hrange]
    ext x
    exact (mem_span_basisOfFractionalIdeal (K := K) (I := I)).symm
  have hσI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (Submodule.span ℤ ({σ ω₀, σ ω₁} : Set ℂ) : Set ℂ) := by
    rw [hI]
    have h := Submodule.map_span σ.toAddMonoidHom.toIntLinearMap ({ω₀, ω₁} : Set K)
    rw [Set.image_pair] at h
    have h' := congrArg (fun p : Submodule ℤ ℂ => (p : Set ℂ)) h
    simpa [Submodule.map_coe] using h'
  have h0 : σ ω₀ ≠ 0 := (map_ne_zero σ).mpr (b.ne_zero _)
  set t : ℂ := σ ω₁ / σ ω₀
  have ht : t.im ≠ 0 := im_div_ne_zero_of_basis σ hσ b e
  have himage : (fun z => (σ ω₀)⁻¹ * z) '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) =
      latticeOf t := by
    rw [hσI, image_mul_span_pair, inv_mul_cancel₀ h0, latticeOf, inv_mul_eq_div]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨⟨-t, by simpa using hneg⟩, (σ ω₀)⁻¹, inv_ne_zero h0, ?_⟩
    show _ = latticeOf (-t)
    rw [latticeOf_neg, himage]
  · exact ⟨⟨t, hpos⟩, (σ ω₀)⁻¹, inv_ne_zero h0, himage⟩
end GroundTheory.Heights₂.Theta
