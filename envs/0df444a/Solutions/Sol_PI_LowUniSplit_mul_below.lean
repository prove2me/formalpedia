-- Prove2me | solution 1 for PI.LowUniSplit.mul_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:34.623504+00:00
-- url     : https://prove2.me/submissions/ac08ac81-7327-4d7f-a079-ff2f8074dbd6

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.LowUniSplit
theorem _root_.solution {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    {i j : Fin m} (hji : j < i) :
    (a * b) i j = a i j + b i j + ∑ k : Btw i j, a i k.1 * b k.1 j := by
  rw [Matrix.mul_apply]
  have hpt : ∀ k : Fin m, a i k * b k j =
      (if k = j then a i j else 0) + (if k = i then b i j else 0) +
        (if j < k ∧ k < i then a i k * b k j else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      simp [hb.2, ne_of_lt hji]
    by_cases hki : k = i
    · subst hki
      simp [ha.2, hkj]
    rcases lt_or_gt_of_ne hkj with h1 | h1
    · simp [hkj, hki, hb.1 k j h1, not_lt.mpr h1.le]
    rcases lt_or_gt_of_ne hki with h2 | h2
    · simp [hkj, hki, h1, h2]
    · simp [hkj, hki, ha.1 i k h2, not_lt.mpr h2.le]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun k => by simp) _
end PI.LowUniSplit
