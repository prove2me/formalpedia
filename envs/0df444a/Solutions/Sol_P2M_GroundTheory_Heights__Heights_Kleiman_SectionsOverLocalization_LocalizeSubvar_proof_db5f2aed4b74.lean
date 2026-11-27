-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_proof_db5f2aed4b74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:19.60238+00:00
-- url     : https://prove2.me/submissions/90f2f8a2-8687-451e-a50a-eff1331e3727

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeSubvar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca


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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace LocalizeSubvar
theorem _root_.solution : LocalizeSubvar.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x pp' e hle h
  have := h.isPrime
  refine
    { isPrime := Ideal.comap_isPrime _ _
      homog := ?_
      le := ?_
      relevant := ?_
      dim := ?_ }
  · intro g hg d
    rw [Ideal.mem_comap, ← LocalizeSubvar.homogeneousComponent_map]
    exact h.homog _ hg d
  · intro g hg
    rw [Kleiman.primeOf_eq, RingHom.mem_ker] at hg
    rw [Ideal.mem_comap]
    apply h.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    rw [Kleiman.cone_eq, Kleiman.coneGen] at hg
    exact hg
  · obtain ⟨i, hi⟩ := h.relevant
    exact ⟨i, by rw [Ideal.mem_comap, map_X]; exact hi⟩
  · rw [← h.dim]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
      ⟨Ideal.quotientMap_injective, LocalizeSubvar.quotientMap_surjective S 𝔪 O N pp' hle⟩)
end LocalizeSubvar
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
