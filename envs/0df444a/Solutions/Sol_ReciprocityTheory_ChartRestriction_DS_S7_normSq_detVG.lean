-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.normSq_detVG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:45.040718+00:00
-- url     : https://prove2.me/submissions/8e4f6eaa-c344-4c48-ab7c-6f835eef09ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
private lemma Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
section supnorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end supnorm
section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
end frob
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have hJ := Jm_mul_self_eq_one' ε
  have hJ0 : (Jm ε).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJ
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hdet := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hdet
  have h2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hJ0
    calc star g.det * g.det * (Jm ε).det = star g.det * (Jm ε).det * g.det := by ring
      _ = (Jm ε).det := hdet
      _ = 1 * (Jm ε).det := by ring
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3
end ReciprocityTheory.ChartRestriction.DS.S7
