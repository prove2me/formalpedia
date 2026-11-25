-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:35.344217+00:00
-- url     : https://prove2.me/submissions/6687a025-dafd-4042-b033-907975c5a965

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_isMultiHomog_monomial_b8c6467b5442

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
theorem _root_.solution {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
