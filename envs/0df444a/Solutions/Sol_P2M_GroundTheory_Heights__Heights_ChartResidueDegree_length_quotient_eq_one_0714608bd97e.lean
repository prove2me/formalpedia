-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:49.33139+00:00
-- url     : https://prove2.me/submissions/4df0a86c-d38a-44a0-9506-439dd3f3c389

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree

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
open GroundTheory.Heights₂.Heights.ChartResidueDegree
namespace GroundTheory.Heights₂.Heights.ChartResidueDegree
theorem _root_.solution {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] (𝔓 : Ideal R)
    (hmax : (𝔓.comap (algebraMap O R)).IsMaximal) (hsurj : ∀ x : R, ∃ o : O, x - algebraMap O R o ∈ 𝔓) :
    Module.length O (R ⧸ 𝔓) = 1 := by
  have hs : Function.Surjective (algebraMap O (R ⧸ 𝔓)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨o, ho⟩ := hsurj x
    refine ⟨o, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← neg_sub]
    exact 𝔓.neg_mem ho
  have hkerf : RingHom.ker (Algebra.ofId O (R ⧸ 𝔓)) = 𝔓.comap (algebraMap O R) := by
    ext o
    rw [RingHom.mem_ker, Ideal.mem_comap, Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [← (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId O (R ⧸ 𝔓)) hs).toLinearEquiv.length_eq,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, hkerf]
  exact hmax
end GroundTheory.Heights₂.Heights.ChartResidueDegree
