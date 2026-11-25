-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_proof_47e5fef559fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:08.18708+00:00
-- url     : https://prove2.me/submissions/de127f82-432f-4a22-9190-fd24cecd2c2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_secs_eq_72584acc7dfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_restrictData_comp_e303461df737
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_redHom_ratio_0cab988a2124
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_residue_6f46e5b5679e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Restrict_proof_9254d696b6ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution (hSC : SurjectiveClosed.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) : RestrLenRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hsp pp e hW Q Q' r hr
  have := hW.isPrime
  obtain ⟨j, hjX⟩ := hW.relevant
  have hyj : y j ≠ 0 := fun h0 => hjX (hW.le
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by rw [aeval_X, h0])))
  have hxj : x j ≠ 0 := hxy j hyj
  have hle : primeOf (S := k) x ≤ pp := hsp.trans hW.le
  have : (chartPrime pp hyj).IsPrime :=
    (PrimeFiltration.Point.proof k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX).1
  obtain ⟨K'', _, _, ψ, hker⟩ := exists_residue (k := k) (chartPrime pp hyj)
  have hyz : ∀ i, ψ (ratio hyj i) ≠ 0 → y i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := k) hyj i = 0 := Subtype.ext (show y i / y j = 0 by rw [h0, zero_div])
    rw [this, map_zero]

  obtain ⟨QW, rW, hQW⟩ :=
    PrimeFiltration.Restrict.proof k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX K'' ψ hker hyz Q'
  have hRW : RestrictData Q'.toSubSystem hyz QW.toSubSystem rW :=
    ⟨fun I => (hQW I).1, fun I => (hQW I).2.1, fun I => (hQW I).2.2.1, fun I => (hQW I).2.2.2⟩
  have hRxW := restrictData_comp hr hRW

  have hkerx := ker_comp_redHom hsp hxy hyj pp hW.le hjX ψ hker
  have hpt : (fun i => (ψ.comp (redHom hsp hxy hyj)) (ratio hxj i)) = fun i => ψ (ratio hyj i) := by
    funext i
    rw [AlgHom.comp_apply, redHom_ratio]
  have key : ∀ (zz : Fin (N + 1) → K''),
      (fun i => (ψ.comp (redHom hsp hxy hyj)) (ratio hxj i)) = zz →
      ∀ (hxz : ∀ i, zz i ≠ 0 → x i ≠ 0) (QW' : LineBundle k zz) (rr : Ω → K''),
      RestrictData Q.toSubSystem hxz QW'.toSubSystem rr → ∀ c : ℤ,
      Nonempty (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 0 ≃ₗ[k] (QW'.twist (twistSys k zz c)).H 0) := by
    rintro zz rfl hxz QW' rr hR c
    exact hRQ k Ω N x pp hW.isPrime hW.homog hle j hxj hjX K'' (ψ.comp (redHom hsp hxy hyj)) hkerx hxz
      Q QW' rr hR c 0
  obtain ⟨c₁, hc₁⟩ := hSC k Ω N x Q pp hW.homog
  obtain ⟨c₂, hc₂⟩ := hSC k K' N y Q' pp hW.homog
  refine Filter.eventually_atTop.mpr ⟨max c₁.toNat c₂.toNat, fun c hc => ?_⟩
  have h1 : c₁ ≤ (c : ℤ) :=
    (Int.self_le_toNat c₁).trans (by exact_mod_cast (le_max_left _ _).trans hc)
  have h2 : c₂ ≤ (c : ℤ) :=
    (Int.self_le_toNat c₂).trans (by exact_mod_cast (le_max_right _ _).trans hc)
  obtain ⟨ex⟩ := key _ hpt _ QW (rW ∘ r) hRxW c
  obtain ⟨ey⟩ := hRQ k K' N y pp hW.isPrime hW.homog hW.le j hyj hjX K'' ψ hker hyz Q' QW rW hRW c 0
  rw [restrLen, restrLen, length_secs_eq _ _ (hc₂ c h2), length_secs_eq _ _ (hc₁ c h1), ey.length_eq,
    ex.length_eq]
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
