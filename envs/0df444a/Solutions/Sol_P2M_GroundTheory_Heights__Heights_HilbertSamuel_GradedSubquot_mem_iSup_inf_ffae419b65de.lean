-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_mem_iSup_inf_ffae419b65de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:32.965537+00:00
-- url     : https://prove2.me/submissions/119e63c0-84cd-4af5-866d-abb4c171861e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_subset_span_7c286179978d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_monTimes_le_d973d73a9be6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_le_span_monTimes_4833d8b0dfcc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81

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
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN
end GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
