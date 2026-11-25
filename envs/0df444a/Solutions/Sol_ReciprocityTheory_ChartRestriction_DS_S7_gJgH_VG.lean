-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.gJgH_VG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:31.427857+00:00
-- url     : https://prove2.me/submissions/34c76838-c5f5-488a-a3fe-042e0d6856db

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
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by
  have hJ := Jm_mul_self_eq_one' ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.S7
