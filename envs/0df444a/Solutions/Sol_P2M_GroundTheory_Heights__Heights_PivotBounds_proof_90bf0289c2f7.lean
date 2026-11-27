-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotBounds_proof_90bf0289c2f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:30.745625+00:00
-- url     : https://prove2.me/submissions/d117a8c4-3086-4b8a-8717-dd41be33c186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PivotBounds
theorem _root_.solution (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPI : PivotInvDiag.Statement) (hPL : PivotLast.Statement) : PivotBounds.Statement := by
  intro d S hS i
  have h : (i : ℕ) + 1 ≤ d := i.isLt
  set L := S.submatrix (Fin.castLE h) (Fin.castLE h) with hLdef
  have hL : L.PosDef := hS.submatrix (Fin.castLE_injective h)
  have hpiv : pivot L i = pivot S i := by
    unfold pivot
    rw [hLL d S _ h _ le_rfl, hLL d S _ h _ (Nat.le_succ _)]
  have hlast : Fin.castLE h (Fin.last (i : ℕ)) = i := Fin.ext rfl
  refine ⟨?_, ?_⟩
  · have h1 := hPL i L hL (Pi.single (Fin.last (i : ℕ)) 1)
    rw [hpiv] at h1
    have hq : MCSchur.qf L (Pi.single (Fin.last (i : ℕ)) 1) = S i i := by
      unfold MCSchur.qf
      rw [mulVec_single_one, single_one_dotProduct]
      simp [hLdef, hlast]
    simpa [hq] using h1
  · intro ε hε hy
    have hx : ∀ x : Fin ((i : ℕ) + 1) → ℝ, ε * x (Fin.last (i : ℕ)) ^ 2 ≤ MCSchur.qf L x := by
      intro x
      have := hy (Function.extend (Fin.castLE h) x 0)
      have he := (Fin.castLE_injective h).extend_apply x (0 : Fin d → ℝ) (Fin.last (i : ℕ))
      rw [hlast] at he
      rwa [he, ← PivotBounds.qf_submatrix_castLE] at this
    have hinv := MCCusp.inv_diag_le hL (Fin.last (i : ℕ)) hε hx
    have hone := hPI i L hL
    have hpos : 0 < L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) := hL.inv.diag_pos
    rw [hpiv] at hone
    set a := L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ))
    have hεa : ε * a ≤ 1 := by
      rw [le_div_iff₀ hε] at hinv
      linarith
    have hp : 0 < pivot S i := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    nlinarith
end PivotBounds
end GroundTheory.Heights₂.Heights
