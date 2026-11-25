-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:55.284616+00:00
-- url     : https://prove2.me/submissions/5f00f21c-349f-4ca7-af3e-2d5ec63918a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution {I K : Chart x} (h : I.1 ⊆ K.1) {a : Ω}
    (ha : a ∈ idealMod pp K) :
    ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧ (u : Ω) * a ∈ idealMod pp I := by
  obtain ⟨g, m, e, hg, hm, hge, hme, rfl⟩ := idealMod_mem_form pp K ha
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hm0 := eval_ne_zero_of_mem_monos K hm
  have hX0 : aeval x (X i ^ e : Poly k N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x m / aeval x (X i ^ e), m, X i ^ e, e, pow_mem (X_mem_monos hi) e, hme,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x m, X i ^ e, m, e, hm, isHomogeneous_X_pow i e, hme, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x m / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x m) = 1
    field_simp
  · change aeval x m / aeval x (X i ^ e) * (aeval x g / aeval x m) ∈ idealMod pp I
    refine Submodule.subset_span ⟨g, X i ^ e, e, hg, pow_mem (X_mem_monos hi) e, hge,
      isHomogeneous_X_pow i e, ?_⟩
    field_simp
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
