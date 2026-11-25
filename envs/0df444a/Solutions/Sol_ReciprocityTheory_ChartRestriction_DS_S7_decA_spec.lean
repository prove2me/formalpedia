-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:17.012627+00:00
-- url     : https://prove2.me/submissions/6ea107d6-9e8e-45b9-8507-270f3d35ea78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℝ), U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ := by
  obtain ⟨h1, h2⟩ := hY
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hH : Yᴴ = Y := by
    unfold inG at h1
    have h3 : Yᴴ * Jm ε = Y * Jm ε := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Y * Jm ε * Jm ε := by rw [h3]
      _ = Y := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hA : Y.IsHermitian := hH
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, (hA.eigenvectorUnitary).2, ?_⟩
  first
    | exact hA.spectral_theorem
    | simpa [Matrix.star_eq_conjTranspose] using hA.spectral_theorem
    | (conv_lhs => rw [hA.spectral_theorem]); rfl
end ReciprocityTheory.ChartRestriction.DS.S7
