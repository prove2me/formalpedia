-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:27.840872+00:00
-- url     : https://prove2.me/submissions/91e698fd-5159-4fcc-ba28-17444b833291

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
theorem _root_.solution {M : Type} {r : ℕ} (f : ℕ → M) (j : Fin r) :
    (fun l : Fin r => f l) '' {l | l < j} = f '' {l : ℕ | l < j} := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Fin.lt_def.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, lt_trans hl j.2⟩, Fin.lt_def.mpr hl, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
