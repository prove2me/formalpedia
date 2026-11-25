-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:35.025195+00:00
-- url     : https://prove2.me/submissions/d8acbf41-5f8b-4dd8-bae7-8acc0eae04a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_recR_congr_645a04940dee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) :
    famI P (n + 1) (Fin.snoc L A) =
      recR famI P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
        recR famI P L (segreLine (shift A)) (secOf P fun _ => shift A) := by
  have hc : ∀ (B : HermLine ι) (s : MRing ι), recR (lift (fam n)) P L B s = recR famI P L B s :=
    fun B s => recR_congr (fun W L' => lift_self (fam n) W L') P L B s
  have hs : famI P (n + 1) (Fin.snoc L A) = step (fam n) P L A := by
    simp only [famI, fam, Fin.init_snoc, Fin.snoc_last]
  rw [hs, step, hc, hc]
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
