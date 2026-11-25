-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:20.384557+00:00
-- url     : https://prove2.me/submissions/936df6b5-2c18-462a-bb8b-87a66dedb801

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (fun l => if l = k then 1 else 0) := by
  classical
  intro m hm l
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    simp [Finsupp.single_apply]
  · have : ∀ j : ι l, (Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) ⟨l, j⟩ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hl (congrArg Sigma.fst h).symm
    simp [this, hl]
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
