-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:47.911237+00:00
-- url     : https://prove2.me/submissions/1444dfc8-07c0-44f4-af75-9c72979f0860

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {R : Type*} [CommRing R] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {φ ψ : E →+* R}
    (hF : ∀ c, φ (algebraMap F E c) = ψ (algebraMap F E c)) (hxe : φ x = ψ x) : φ = ψ := by
  ext y
  rw [← (basisOneOf hx).sum_repr y, Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one,
    Algebra.smul_def, Algebra.smul_def]
  simp only [map_add, map_mul, hF, hxe, map_one]
end GroundTheory.Heights₂.Theta
