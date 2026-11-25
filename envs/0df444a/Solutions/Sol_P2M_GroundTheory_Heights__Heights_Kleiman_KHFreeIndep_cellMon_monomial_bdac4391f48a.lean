-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_cellMon_monomial_bdac4391f48a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:44.580035+00:00
-- url     : https://prove2.me/submissions/e8ad1902-23dc-4810-aaed-3a1b0a18cdc0

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
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
theorem _root_.solution {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep
