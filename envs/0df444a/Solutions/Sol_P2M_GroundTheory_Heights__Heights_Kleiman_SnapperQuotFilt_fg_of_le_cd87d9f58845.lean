-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_le_cd87d9f58845
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:02:44.163154+00:00
-- url     : https://prove2.me/submissions/8927711b-9e71-408e-ae3a-469f6fd0a656

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08


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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution [IsNoetherianRing S] (F G : SubFamily S x E) (hF : ∀ I, (F.sub I).FG)
    (hle : ∀ I, G.sub I ≤ F.sub I) (I : Chart x) : (G.sub I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have := Domination.isNoetherianRing_chartRing (S := S) hxi
  have : IsNoetherian (chartRing S x (singleChart hxi)) (F.sub (singleChart hxi)) :=
    isNoetherian_of_fg_of_noetherian _ (hF _)
  exact fg_of_single G I hi hxi (Submodule.FG.of_le_of_isNoetherian (hle _))
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
