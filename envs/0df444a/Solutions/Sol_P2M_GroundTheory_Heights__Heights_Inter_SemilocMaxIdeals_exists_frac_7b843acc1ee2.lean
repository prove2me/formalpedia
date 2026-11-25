-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_frac_7b843acc1ee2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:55.658475+00:00
-- url     : https://prove2.me/submissions/222beb38-e9c1-4fbd-852f-af652bffd54e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_one_notMem_f81969489234

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution (h𝒲 : ∀ W ∈ 𝒲, W.IsPrime) (x : semiLocRing P 𝒲) :
    ∃ (u w : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog w a ∧ w ∉ P ∧ (∀ W ∈ 𝒲, w ∉ W) ∧
      (x : FractionRing (MRing ι ⧸ P)) * fracHom P w = fracHom P u := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩ := hx
    exact ⟨u, w, a, hu, hwa, fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h), hwW,
      IsLocalization.mk'_spec _ _ _⟩
  | zero =>
    exact ⟨0, 1, 0, homog_zero 0, homog_one, one_notMem ‹_›, fun W hW => one_notMem (h𝒲 W hW), by simp⟩
  | one =>
    exact ⟨1, 1, 0, homog_one, homog_one, one_notMem ‹_›, fun W hW => one_notMem (h𝒲 W hW), by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    obtain ⟨u', w', a', hu', hw', hwP', hwW', hy⟩ := hy
    refine ⟨u * w' + u' * w, w * w', a + a', homog_add (homog_mul hu hw') ?_, homog_mul hw hw',
      notMem_mul ‹_› hwP hwP', fun W hW => notMem_mul (h𝒲 W hW) (hwW W hW) (hwW' W hW), ?_⟩
    · rw [add_comm a a']
      exact homog_mul hu' hw
    · simp only [map_add, map_mul]
      rw [← hx, ← hy]
      ring
  | neg x _ hx =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    exact ⟨-u, w, a, homog_neg hu, hw, hwP, hwW, by rw [map_neg, ← hx, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, w, a, hu, hw, hwP, hwW, hx⟩ := hx
    obtain ⟨u', w', a', hu', hw', hwP', hwW', hy⟩ := hy
    refine ⟨u * u', w * w', a + a', homog_mul hu hu', homog_mul hw hw', notMem_mul ‹_› hwP hwP',
      fun W hW => notMem_mul (h𝒲 W hW) (hwW W hW) (hwW' W hW), ?_⟩
    simp only [map_mul]
    rw [← hx, ← hy]
    ring
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
