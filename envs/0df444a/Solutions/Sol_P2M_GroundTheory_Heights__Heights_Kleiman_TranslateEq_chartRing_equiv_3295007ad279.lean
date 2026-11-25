-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:44.10299+00:00
-- url     : https://prove2.me/submissions/a1a1fa2b-927d-4ffa-bee1-c7c0cc1f766b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace chartRing
theorem _root_.solution (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton, ← chartRingI.equiv]
  rfl
end chartRing
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
