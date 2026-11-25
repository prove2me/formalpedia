-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:19.885745+00:00
-- url     : https://prove2.me/submissions/3c826c57-ff52-4eef-9061-2962a05b1673

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f

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
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomogIdeal I) : ∀ p ∈ integralModel I, ∀ d, homogeneousComponent d p ∈ integralModel I := by
  intro p hp d
  show MvPolynomial.map (algebraMap (𝓞 K) K) (homogeneousComponent d p) ∈ I
  rw [map_homogeneousComponent]
  exact hI _ hp d
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
