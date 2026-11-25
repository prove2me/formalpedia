-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:23.496902+00:00
-- url     : https://prove2.me/submissions/94ba6789-f1f7-4188-8d86-402c5ecef3b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_ker_map_le_span_bd4e93bd4fc2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B)
    (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1)) :
    ∃ h : Matrix (Fin n) (Fin n) (OmegaF P n), h * B.map σ = B.map (iota P n) := by
  set M : Matrix (Fin t) (Fin N1) (FnField P) := Matrix.of fun a j => evalAt (genPt P) (c a j)
  have hmem : ∀ a, (B.map (iota P n)) a ∈ Submodule.span (OmegaF P n) (Set.range (B.map σ)) := by
    intro a
    apply ker_map_le_span σ M B hB.1 hB.2
    have h0 : B a ∈ LinearMap.ker M.mulVecLin := hB.2 ▸ Submodule.subset_span ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h0
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    have h1 := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.of_apply, Pi.zero_apply] at h1 ⊢
    simp only [sigma_evalAt P n σ hσ (hc _ _), mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, h1,
      map_zero, mul_zero]
  choose h hh using fun a => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem a)
  refine ⟨Matrix.of h, ?_⟩
  ext a j
  rw [Matrix.mul_apply, ← hh a]
  simp [Finset.sum_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
