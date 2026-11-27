-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeNefAbove_proof_108955b4bab8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:01.74694+00:00
-- url     : https://prove2.me/submissions/a109176a-a204-4762-ac78-f83505a57dc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeNefAboveSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeRestrLenSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeNefAbove
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace LocalizeNefAbove
theorem _root_.solution (h₁ : LocalizeSubvar.Statement) (h₂ : LocalizeRestrLen.Statement) :
    LocalizeNefAbove.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M hM pp' hJ hpp'
  have hJp : 𝔪.map (C : S →+* Poly S N) ≤
      pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N) := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    change MvPolynomial.map (algebraMap S O) (C m) ∈ pp'
    rw [map_C]
    exact hJ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hm))
  have hL : (![M.baseChange O] : Fin 1 → SubSystem O x Ω) = fun i => (![M] i).baseChange O := by
    funext i; fin_cases i; rfl
  have key : interNum pp' ![M.baseChange O] =
      interNum (pp'.comap (MvPolynomial.map (algebraMap S O) : Poly S N →+* Poly O N)) ![M] := by
    unfold interNum
    congr 1
    funext c
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    rw [hL, baseChange_tensorSub, ← baseChange_twistSys (S := S), ← baseChange_twist]
    exact h₂ S 𝔪 O Ω N x pp' hJ _
  rw [key]
  exact hM _ hJp (h₁ S 𝔪 O Ω N x pp' 1 hJ hpp')
end LocalizeNefAbove
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
