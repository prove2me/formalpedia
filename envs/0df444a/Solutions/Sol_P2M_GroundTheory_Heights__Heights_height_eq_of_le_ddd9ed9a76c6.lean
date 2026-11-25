-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:32.271893+00:00
-- url     : https://prove2.me/submissions/5a6fe7db-4903-423f-84d2-4d377868ec22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_finiteTerm_algebraMap_b2a1b9f5b23a

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
open NumberField Module
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx0 : BlockNonzero x)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (hx : ∀ k i, x k i ∈ L) :
    height A x = ((finrank ℚ L : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace L, finiteTerm A w (coordIn L x hx) +
        ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordIn L x hx k i))) := by
  have hKL : coordField x ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨v, rfl⟩; exact hx v.1 v.2)
  let _ : Algebra (coordField x) L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  have hco : coordIn L x hx = fun k i ↦ algebraMap (coordField x) L (coordVec x k i) := rfl
  have hblock : BlockNonzero (coordVec x) := fun k h ↦ hx0 k (funext fun i ↦ by
    have := congrFun h i
    exact congrArg Subtype.val this)
  have hfin := finsum_finiteTerm_algebraMap (L := L) A hblock
  have harch := sum_embeddings_restrict (K := coordField x) (L := L)
    (fun τ ↦ Real.log (A.metric fun k i ↦ τ (coordVec x k i)))
  have hdeg := Module.finrank_mul_finrank ℚ (coordField x) L
  rw [hco, hfin]
  change _ = _ * (_ + ∑ σ : L →+* ℂ, Real.log (A.metric fun k i ↦
    (σ.comp (algebraMap (coordField x) L)) (coordVec x k i)))
  rw [harch, ← hdeg]
  unfold height
  have h1 : (0 : ℝ) < finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have h2 : (0 : ℝ) < finrank (coordField x) L := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp
  rfl
end GroundTheory.Heights₂.Heights
