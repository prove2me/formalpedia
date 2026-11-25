-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:50.980344+00:00
-- url     : https://prove2.me/submissions/11dedfa7-e102-4880-9150-d4e6381494d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PPointHeightDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0


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
open NumberField Module Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : HermLine n) {K' : Type*} [Field K'] [NumberField K']
    (τ : K' →+* AlgebraicClosure ℚ) (y : Cone n K') (hy : BlockNonzero y) :
    height A (fun k i ↦ τ (y k i)) = ((finrank ℚ K' : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace K', finiteTerm A w y +
        ∑ σ : K' →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i))) := by
  set τ' : K' →ₐ[ℚ] AlgebraicClosure ℚ := τ.toRatAlgHom
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := τ'.fieldRange
  let e : K' ≃ₐ[ℚ] L := AlgEquiv.ofInjectiveField τ'
  have : FiniteDimensional ℚ L := e.toLinearEquiv.finiteDimensional
  have : NumberField L := {}
  have hx : ∀ k i, τ (y k i) ∈ L := fun k i ↦ ⟨y k i, rfl⟩
  have hx0 : BlockNonzero (fun k i ↦ τ (y k i)) := fun k h ↦ hy k (funext fun i ↦ by
    have := congrFun h i
    exact τ.injective (by simpa using this))
  rw [height_eq_of_le A hx0 L hx]
  let _ : Algebra L K' := e.symm.toRingHom.toAlgebra
  have : IsScalarTower ℚ L K' := IsScalarTower.of_algebraMap_eq fun q ↦ by
    change algebraMap ℚ K' q = e.symm (algebraMap ℚ L q)
    rw [AlgEquiv.commutes]
  have he : ∀ k i, algebraMap L K' (coordIn L (fun k i ↦ τ (y k i)) hx k i) = y k i := by
    intro k i
    change e.symm _ = _
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  have hblock : BlockNonzero (coordIn L (fun k i ↦ τ (y k i)) hx) := fun k h ↦ hx0 k (funext fun i ↦ by
    have := congrFun h i
    exact congrArg Subtype.val this)
  have hfin := finsum_finiteTerm_algebraMap (K := L) (L := K') A hblock
  have harch := sum_embeddings_restrict (K := L) (L := K')
    (fun σ ↦ Real.log (A.metric fun k i ↦ σ (coordIn L (fun k i ↦ τ (y k i)) hx k i)))
  simp only [RingHom.comp_apply, he] at hfin harch
  have hdeg := Module.finrank_mul_finrank ℚ L K'
  rw [hfin, harch, ← hdeg]
  have h1 : (0 : ℝ) < finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h2 : (0 : ℝ) < finrank L K' := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp
end GroundTheory.Heights₂.Heights
