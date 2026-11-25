-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_mul_not_mem_91abb2477222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:57.956311+00:00
-- url     : https://prove2.me/submissions/ff1bb1aa-d6ad-4ee4-8e49-051eae571ad4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm

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
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution {P Z Z' : Submodule R Ω} (hZ : Z * Z' = 1) {z : Ω} (hz : z ∈ Z)
    (hzP : z ∉ P * Z) : ∃ z' ∈ Z', z * z' ∈ (1 : Submodule R Ω) ∧ z * z' ∉ P := by
  by_contra hcon
  push Not at hcon
  apply hzP
  have h1 : Submodule.span R {z} * Z' ≤ P := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [smul_mul_assoc]
    refine P.smul_mem r (hcon n hn ?_)
    rw [← hZ]
    exact Submodule.mul_mem_mul hz hn
  have h2 : z ∈ Submodule.span R {z} * Z' * Z := by
    rw [mul_assoc, mul_comm Z' Z, hZ, mul_one]
    exact Submodule.mem_span_singleton_self z
  exact mul_le_mul' h1 le_rfl h2
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
