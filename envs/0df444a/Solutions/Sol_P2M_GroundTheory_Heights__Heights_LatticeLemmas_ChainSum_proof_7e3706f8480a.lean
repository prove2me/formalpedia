-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_proof_7e3706f8480a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:16:13.997186+00:00
-- url     : https://prove2.me/submissions/80fd451b-100b-40c5-8025-ef476d616853

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace ChainSum
theorem _root_.solution (h1 : ExactSequence.Statement.{u, v}) : ChainSum.Statement.{u, v} := by
  intro K _ _ M k
  induction k with
  | zero =>
    intro c h0 _ _
    have hl : c (Fin.last 0) = ⊤ := h0
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero, hl, ChainSum.deg_sub_top]
  | succ k ih =>
    intro c h0 hmono hc
    have hmono' : Antitone fun a : Fin (k + 1) ↦ c a.castSucc :=
      fun a b hab ↦ hmono (Fin.castSucc_le_castSucc_iff.mpr hab)
    have hIH := ih (fun a ↦ c a.castSucc) h0 hmono' fun a ↦ hc _
    have hle : c (Fin.last (k + 1)) ≤ c (Fin.last k).castSucc :=
      hmono (Fin.castSucc_lt_last _).le
    have hE := h1 K (M.sub (c (Fin.last k).castSucc))
      ((c (Fin.last (k + 1))).comap (c (Fin.last k).castSucc).subtype)
      ((hc (Fin.last (k + 1))).comap_subtype _)
    rw [ChainSum.deg_sub_comap M hle] at hE
    rw [Fin.sum_univ_castSucc, hIH, hE, add_assoc]
    congr 1
    rw [add_comm]
    rfl
end ChainSum
end GroundTheory.Heights₂.Heights.LatticeLemmas
