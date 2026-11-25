-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:26.786852+00:00
-- url     : https://prove2.me/submissions/ceb944c2-4b87-4779-b2a0-1787414cfeab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_chartRing_fg_1c4b759fa1c8

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
theorem _root_.solution [IsNoetherianRing S] (I : Chart x) : IsNoetherianRing (chartRing S x I) := by
  have : Algebra.FiniteType S (chartRing S x I) := ⟨(Subalgebra.fg_top _).mpr (chartRing_fg I)⟩
  exact Algebra.FiniteType.isNoetherianRing S _
end GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
