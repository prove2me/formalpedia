-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:50.318565+00:00
-- url     : https://prove2.me/submissions/8af5974e-cc8d-4be3-9b76-f17aab3d086a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveComplexPoint_eval__smul_homog_35af9e8e8d54


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
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    σ (evalAt (genPt P) f) = (∏ k, lam P n (Sum.inl k) ^ a k) * iota P n (evalAt (genPt P) f) := by
  have key : ∀ φ : FnField P →+* OmegaF P n,
      φ (evalAt (genPt P) f) = eval₂ (Int.castRingHom _) (fun p => φ (genPt P p)) f := by
    intro φ
    rw [evalAt, eval_map, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [key σ, key (iota P n)]
  simp only [hσ]
  rw [show (fun p : Σ k, ι k => iota P n (genPt P p) * lam P n (Sum.inl p.1)) =
      fun p => lam P n (Sum.inl p.1) * iota P n (genPt P p) from funext fun _ => mul_comm _ _]
  exact HeightsSet.CurveComplexPoint.eval₂_smul_homog f a hf (fun k => lam P n (Sum.inl k))
    (fun p => iota P n (genPt P p))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
