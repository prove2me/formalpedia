-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_lex_of_isMultiHomogIdeal_383ee6f0c2b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:06.182666+00:00
-- url     : https://prove2.me/submissions/226e348f-5a4e-4191-be9c-878440c8a90a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro i r hr
  change ((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i :
    MRing ι R) ∈ I
  rw [weightedDecomposition.decompose'_apply]
  obtain ⟨b, rfl⟩ := lexRelabel_surjective e i
  rw [weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact hI r hr b
end GroundTheory.Heights₂.Heights.NumbersDVR
