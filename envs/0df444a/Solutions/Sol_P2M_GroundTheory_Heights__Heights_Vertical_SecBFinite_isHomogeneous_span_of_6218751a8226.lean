-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:47.437855+00:00
-- url     : https://prove2.me/submissions/469c1304-45f2-42b7-ab40-c6d8449ff3a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

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
variable {σ R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {s : Set (MvPolynomial σ R)} (h : ∀ x ∈ s, ∃ d, x.IsHomogeneous d) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ R) :=
  Ideal.homogeneous_span _ _ fun x hx =>
    let ⟨d, hd⟩ := h x hx
    ⟨d, (mem_homogeneousSubmodule d x).mpr hd⟩
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
