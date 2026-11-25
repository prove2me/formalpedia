-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_shift_injective_2ece92e8e32a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:23.753693+00:00
-- url     : https://prove2.me/submissions/25e2d5d4-e1c5-463e-86f8-515a1c67e492

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeIndep

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
theorem _root_.solution (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
