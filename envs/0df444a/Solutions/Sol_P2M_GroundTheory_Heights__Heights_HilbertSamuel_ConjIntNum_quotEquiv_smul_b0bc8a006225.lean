-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:52.202968+00:00
-- url     : https://prove2.me/submissions/83705f68-cba7-4da3-96e4-d187878fbd08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
theorem _root_.solution (τ : F ≃+* F) (J : Ideal (MRing ι F)) (c : F) (x : MRing ι F ⧸ J) :
    quotEquiv τ J (c • x) = τ c • quotEquiv τ J x := by
  have hs : ∀ (I : Ideal (MRing ι F)) (a : F) (g : MRing ι F),
      a • Ideal.Quotient.mk I g = Ideal.Quotient.mk I (C a * g) := fun I a g => by
    rw [← smul_eq_C_mul]
    exact (map_smul (Ideal.Quotient.mkₐ F I) a g).symm
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [hs, quotEquiv_mk, quotEquiv_mk, hs, map_mul, map_C]
  rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
