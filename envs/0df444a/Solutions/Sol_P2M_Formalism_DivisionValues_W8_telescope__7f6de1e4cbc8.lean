-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:06.462127+00:00
-- url     : https://prove2.me/submissions/32162cff-f151-4605-9469-a398f5c24ab7

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
private lemma sum_castSucc_sub_succ_eq_sub_last {n : ℕ} (c : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (c i.castSucc - c i.succ) = c 0 - c (Fin.last n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : ∑ i : Fin m, (c i.castSucc.castSucc - c i.succ.castSucc) =
        c (0 : Fin (m + 1)).castSucc - c (Fin.last m).castSucc := ih (fun j => c j.castSucc)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [h]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring
end W8
open W8
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {n : ℕ} {c : Fin (n + 1) → ℝ} {c' : Fin n → ℝ} {S : ℝ}
    (h : Formalism.LatticeIndexTer.Interlaced n c c' S) : ∑ i : Fin n, (c' i - c i.succ) ≤ S := by
  have hsum : ∑ i : Fin n, (c' i - c i.succ) ≤ ∑ i : Fin n, (c i.castSucc - c i.succ) :=
    Finset.sum_le_sum fun i _ => by linarith [(h.2 i).1]
  rw [sum_castSucc_sub_succ_eq_sub_last] at hsum
  linarith [(h.1 0).2, (h.1 (Fin.last n)).1]
end Formalism.DivisionValues.W8
