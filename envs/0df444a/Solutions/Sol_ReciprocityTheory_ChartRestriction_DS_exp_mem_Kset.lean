-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exp_mem_Kset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:17.857389+00:00
-- url     : https://prove2.me/submissions/14709cc3-d70f-42a3-8cf3-b1066b721a24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
open scoped Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
private theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private theorem conjTranspose_eq_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm, mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, neg_mul]
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    NormedSpace.exp Z ∈ Kset ε := by
  have hZh : Zᴴ = -Z := by
    rw [conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1
    rw [← Matrix.exp_conjTranspose, hZh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)
end ReciprocityTheory.ChartRestriction.DS
