-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:08.627804+00:00
-- url     : https://prove2.me/submissions/3fd64937-f4d8-4f33-bc28-a6dd6630b1ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
theorem _root_.solution {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  have hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem
  rw [← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d),
    ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]
  exact this
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
