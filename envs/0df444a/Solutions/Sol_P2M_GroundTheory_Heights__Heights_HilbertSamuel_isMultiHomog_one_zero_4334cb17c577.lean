-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultiHomog_one_zero_4334cb17c577
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:33.584585+00:00
-- url     : https://prove2.me/submissions/99e911da-4e2a-476b-950e-a3a32f6162c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
omit [Fintype K] [∀ k, Subsingleton (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution : IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]
end GroundTheory.Heights₂.Heights.HilbertSamuel
