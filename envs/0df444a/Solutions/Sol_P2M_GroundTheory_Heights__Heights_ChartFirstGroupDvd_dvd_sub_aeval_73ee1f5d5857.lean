-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:21.787535+00:00
-- url     : https://prove2.me/submissions/3aaf21c8-c4d1-47a6-b284-6c5701426135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupDvd

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
namespace GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (a : MvPolynomial (Fin n) R)
    (σ : Fin n → MvPolynomial (Fin n) R) (hσ : ∀ m, a ∣ σ m - X m) (P : MvPolynomial (Fin n) R) :
    a ∣ P - aeval σ P := by
  set π := Ideal.Quotient.mk (Ideal.span {a})
  have h : π.comp (aeval σ).toRingHom = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π]
    · intro m
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, π]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hσ m
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  exact (RingHom.congr_fun h P).symm
end GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
