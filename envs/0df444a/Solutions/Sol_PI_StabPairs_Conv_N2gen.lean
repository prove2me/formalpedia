-- Prove2me | solution 1 for PI.StabPairs.Conv.N2gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:43.446094+00:00
-- url     : https://prove2.me/submissions/647e02b5-ad3c-40ca-8cdf-5980eedf4eb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r)
    {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (hM : M * Ff k r z = Ff k r z * u)
    (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    M i (eI k r a) = if i = eI k r a then 1 else 0 := by
  classical
  have hfa : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by
    unfold fvec
    rw [dif_pos (by simp)]
    rfl
  have h1 := congrFun (congrFun hM i) (Fin.castSucc a)
  have hL : (M * Ff k r z) i (Fin.castSucc a) = M i (eI k r a) := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply, hfa]
    simp [bvec, Pi.single_apply]
  have hR : (Ff k r z * u) i (Fin.castSucc a) = if i = eI k r a then 1 else 0 := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.castSucc a)]
    · rw [hu.2, mul_one, hfa]
      simp [bvec, Pi.single_apply]
    · intro b _ hb
      by_cases hba : Fin.castSucc a < b
      · rw [hu.1 _ _ hba, mul_zero]
      · have hlt : b.val < a.val := by
          have h2 : b < Fin.castSucc a := lt_of_le_of_ne (not_lt.mp hba) hb
          exact h2
        have hbr : b.val < r := by omega
        have : fvec k r z b i = 0 := by
          unfold fvec
          rw [dif_pos hbr]
          exact Pi.single_eq_of_ne (fun h' => by
            have := congrArg Fin.val h'
            simp [eI] at this
            omega) _
        rw [this, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [← hL, h1, hR]
end PI.StabPairs.Conv
