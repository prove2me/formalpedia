-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthQuotientDet_proof_3ec1c6b761f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:28.419748+00:00
-- url     : https://prove2.me/submissions/32a6de56-d23a-450d-8af0-5859743b9f37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthQuotientDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af

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
open Module
namespace GroundTheory.Heights₂.Heights
namespace LengthQuotientDet
theorem _root_.solution : LengthQuotientDet.Statement := by
  intro O _ _ _ M _ _ _ _ φ hdet
  classical
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hdet))
  set ι := Module.Free.ChooseBasisIndex O M
  let b := Module.Free.chooseBasis O M
  have hrank : finrank O (LinearMap.range φ) = finrank O M := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hlen : Module.length O (M ⧸ LinearMap.range φ) = ∑ i, Ring.ord O (a i) := by
    rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let v : Basis ι O M := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hv : ∀ i, φ (v i) = a i • b' i := by
    intro i
    have h1 : φ (v i) = ((LinearEquiv.ofInjective φ hinj) (v i) : M) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [v, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det v = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑v) = fun i => a i • b' i := funext hv
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  have hassoc : Associated (LinearMap.det φ) (∏ i, a i) := by
    obtain ⟨u, hu⟩ := b'.isUnit_det v
    exact ⟨u, by rw [hu]; exact hdetprod⟩
  rw [hlen, Ring.ord_eq_of_associated hassoc, LengthQuotientDet.ord_prod _ _ ha]
end LengthQuotientDet
end GroundTheory.Heights₂.Heights
