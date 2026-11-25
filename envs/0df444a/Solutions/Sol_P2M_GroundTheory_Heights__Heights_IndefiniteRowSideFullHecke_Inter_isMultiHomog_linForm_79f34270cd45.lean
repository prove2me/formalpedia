-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_linForm_79f34270cd45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:49.491977+00:00
-- url     : https://prove2.me/submissions/e53dd50f-5ed1-4920-9c07-fbcc44079014

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreBlock_inl_subsingleton_2ebb000443cf

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {Φ : Type} [Field Φ] {N1 : ℕ}
    (μ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Φ) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver Φ (fibreIdx (PBlk ι N1) Sum.inl)) fun _ => 1 := by
  classical
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_inl_subsingleton _ _
  simp [Finsupp.single_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
