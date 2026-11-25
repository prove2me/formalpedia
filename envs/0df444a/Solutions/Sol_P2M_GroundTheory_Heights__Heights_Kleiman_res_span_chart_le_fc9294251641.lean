-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_span_chart_le_fc9294251641
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:12.588574+00:00
-- url     : https://prove2.me/submissions/fbc36e42-9193-4f83-8bd8-ed04bf1f7f7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) {z : Ω}
    (hz : z ∈ Submodule.span (chartRing S x I) R) : z ∈ Submodule.span (chartRing S x J) R := by
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J) R)
    (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _)
    (fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv) ?_ hz
  intro c u _ hu
  have := Submodule.smul_mem _ (chartIncl hIJ c) hu
  rw [chartRing_smul_def] at this ⊢
  exact this
end GroundTheory.Heights₂.Heights.Kleiman
