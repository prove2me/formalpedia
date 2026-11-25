-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:21.366403+00:00
-- url     : https://prove2.me/submissions/4169bdf9-445b-4685-b262-2eb7152f7611

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k
end GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
