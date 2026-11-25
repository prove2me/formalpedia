-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:39.715002+00:00
-- url     : https://prove2.me/submissions/d61c06b0-7b56-4744-8cb0-4c74a3a8cb69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_minor_ne_zero_143e4e8206ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMap_X_inr_78c69b7b7f9a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984

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
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B)
    (j : Fin (n - 1)) : ∃ S : PluckerBlocks N1 n j, (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) ∉ flagIdeal P B := by
  have hj : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  obtain ⟨S, hS, hne⟩ := exists_minor_ne_zero (B.submatrix (Fin.castLE hj) id)
    (hB.comp _ (Fin.castLE_injective hj))
  refine ⟨⟨S, hS⟩, fun h => hne ?_⟩
  rw [flagIdeal, RingHom.mem_ker, flagMap_X_inr] at h
  have := eval_one_flagMinor P B j ⟨S, hS⟩
  rw [h, map_zero] at this
  exact this.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
