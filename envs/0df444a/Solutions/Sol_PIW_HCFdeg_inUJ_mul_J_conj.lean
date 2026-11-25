-- Prove2me | solution 1 for PIW.HCFdeg.inUJ_mul_J_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:14.599725+00:00
-- url     : https://prove2.me/submissions/a280ce61-fd2e-4f5f-adab-a5f8afda3315

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
section Abstract
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
end Abstract
section Matrices
variable {n : ℕ} (ε : Fin n → Bool)
private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]
end Matrices
end PIW.HCFdeg
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)
namespace PIW.HCFdeg
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by
  have h1 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg)
  calc g * Jm ε * gᴴ = g * Jm ε * gᴴ * (Jm ε * Jm ε) := by rw [Jm_mul_self_eq_one', Matrix.mul_one]
    _ = (g * (Jm ε * gᴴ * Jm ε)) * Jm ε := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, Matrix.one_mul]
end PIW.HCFdeg
