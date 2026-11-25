-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:30.692053+00:00
-- url     : https://prove2.me/submissions/8a89d73b-8f3f-4e99-9351-28323b90f60c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution {M : Type} {r : ℕ} (f : ℕ → M) :
    Set.range (fun l : Fin r => f l) = f '' {l : ℕ | l < r} := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
