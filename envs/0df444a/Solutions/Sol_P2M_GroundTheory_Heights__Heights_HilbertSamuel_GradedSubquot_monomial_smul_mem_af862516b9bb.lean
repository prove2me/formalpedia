-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monomial_smul_mem_af862516b9bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:57.305908+00:00
-- url     : https://prove2.me/submissions/79afa1f1-cea0-41d8-a740-32dbf371e694

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
theorem _root_.solution (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx
end GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
