-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_blk_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:21.483982+00:00
-- url     : https://prove2.me/submissions/5a4f4e05-0d3b-4ec9-8913-cce4822c9348

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_mul_dg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (a c : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a a (1 : ℂ))) =
      blkMinor ε c x * (if ε a = ε c ∧ a ≤ c then 1 + s else 1) := by
  unfold blkMinor
  have hx : (x * (1 + s • single a a (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
      (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
      x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) *
      diagonal (fun q : {d : Fin n // ε d = ε c ∧ d ≤ c} => if (q : Fin n) = a then 1 + s else 1) := by
    ext r q
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, hwmf_mul_dg]
  rw [hx, det_mul, det_diagonal]
  congr 1
  split_ifs with ha
  · rw [Fintype.prod_eq_single (⟨a, ha⟩ : {d : Fin n // ε d = ε c ∧ d ≤ c})]
    · simp
    · intro q hq
      have : (q : Fin n) ≠ a := fun h => hq (Subtype.ext h)
      simp [this]
  · apply Finset.prod_eq_one
    intro q _
    have : (q : Fin n) ≠ a := fun h => ha (h ▸ q.2)
    simp [this]
end ReciprocityTheory.ChartRestriction.DS.HW
