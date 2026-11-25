-- Prove2me | solution 1 for P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:57.986941+00:00
-- url     : https://prove2.me/submissions/18d12109-8e63-4940-adab-630e69ada5f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
namespace BiInvariant
theorem _root_.solution {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) (n : Fin p)
    (t : Fin p → K) (M : Matrix (Fin p) (Fin p) K) (S : Finset (Fin p)) (hS : ∀ b ∈ S, n < b) :
    f (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0) = f M := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
    ext b k
    simp
  | insert b S hb ih =>
    have hn : n ∉ S := fun hh => lt_irrefl _ (hS n (Finset.mem_insert_of_mem hh))
    rw [← ih fun b hb => hS b (Finset.mem_insert_of_mem hb),
      ← h.1 n b (hS b (Finset.mem_insert_self _ _)) (t b)
        (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0)]
    congr 1
    ext u k
    by_cases hu : u = b
    · subst hu
      simp [rowAdd, hb, hn]
    · simp [rowAdd, hu]
end BiInvariant
end GlobalTheory.UnipotentInvariant
