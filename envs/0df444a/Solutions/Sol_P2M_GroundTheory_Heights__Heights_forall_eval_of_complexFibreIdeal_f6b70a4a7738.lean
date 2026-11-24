-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:37.725813+00:00
-- url     : https://prove2.me/submissions/9ed1efa0-52ac-4bc8-85e5-57d8d0cc3b04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_rename_pblk_fcf18dd5a0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {z : Fin n → ℂ}
    (hz : ∀ q ∈ complexFibreIdeal P, eval z q = 0) :
    ∀ f ∈ P, eval (fun p : Σ k, PBlk n k => z p.2) (map (Int.castRingHom ℂ) f) = 0 := by
  intro f hf
  have hre : rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k))
      (rename (fun p : Σ k, PBlk n k => p.2) f) = f := by
    rw [rename_rename]
    exact rename_id_apply f
  have hg : rename (fun p : Σ k, PBlk n k => p.2) f ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, hre]
    exact hf
  have h := hz _ (Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℂ)) hg)
  rw [← hre, eval_map_rename_pblk]
  exact h
end GroundTheory.Heights₂.Heights
