-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CountingPairs.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:34:06.990122+00:00
-- url     : https://prove2.me/submissions/c8aba765-7f1c-415f-bcf9-884f251a59f4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CountingPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.CountingPairs.Priv
private lemma cntGt {k : ℕ} (i : Fin k) :
    (∑ c : Fin k, if i < c then (1:ℤ) else 0) = (k:ℤ) - 1 - i := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun c : Fin k => i < c)) = Finset.Ioi i := by
    ext c; simp
  rw [this, Fin.card_Ioi]
  have := i.isLt
  push_cast [Nat.sub_sub, show 1 + (i:ℕ) ≤ k by omega]
  ring
private lemma cntLt {k : ℕ} (c : Fin k) :
    (∑ i : Fin k, if i < c then (1:ℤ) else 0) = (c:ℤ) := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin k => i < c)) = Finset.Iio c := by
    ext i; simp
  rw [this, Fin.card_Iio]
end UpperTheory.Reformulated.B.CountingPairs.Priv
end

set_option autoImplicit false

open UpperTheory.Reformulated.B.CountingPairs.Priv
namespace UpperTheory.Reformulated.B.CountingPairs
theorem _root_.solution :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by
  intro k l
  have h1 : ∀ c i : Fin k, (if i < c then l i - l c else (0:ℤ))
      = (if i < c then (1:ℤ) else 0) * l i - (if i < c then (1:ℤ) else 0) * l c := by
    intro c i; split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => (if i < c then (1:ℤ) else 0) * l i)]
  simp_rw [← Finset.sum_mul, cntGt, cntLt]
  unfold UpperTheory.Reformulated.B.CountingPairs.rhoPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
end UpperTheory.Reformulated.B.CountingPairs
