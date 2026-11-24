-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:50.40861+00:00
-- url     : https://prove2.me/submissions/77bab414-c166-4b80-81c3-525339deab36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    toSecB e I v (C a) = algebraMap (ParDVR e n v) (SecB e I v)
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  simp only [toSecB, RingHom.comp_apply, MvPolynomial.map_C]
  rw [← IsScalarTower.algebraMap_apply]
  rfl
end GroundTheory.Heights₂.Heights.Vertical
