-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_ga_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:29.164968+00:00
-- url     : https://prove2.me/submissions/a02c2d7d-5b49-4a46-b410-756ecd35f0e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_gram_core
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_castLE_succ_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (Y : Fin (1 + r' + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin (r' + 1) → Fin (2 * r' + k + 1) → ℂ)
    (β : Fin (r' + 1) → ℂ) (h0 : Y 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ b, Y (sc r' b) = κ *ᵥ (liftVec k 1 r' (U b) + β b • es0 k r')) (l : Fin (r' + 1)) :
    Ga k (1 + r') (sc r' l) Y = D ^ 2 * Ga k r' l U := by
  have hle : l.val + 1 + 1 ≤ 1 + r' + 1 := by omega
  have hle' : l.val + 1 ≤ r' + 1 := by omega
  have key := ea_gram_core hκ hD (fun a : Fin (l.val + 1 + 1) => Y (Fin.castLE hle a))
    (fun i : Fin (l.val + 1) => U (Fin.castLE hle' i)) (fun i => β (Fin.castLE hle' i))
    (by simp only [Fin.castLE_zero]; exact h0)
    (fun i => by simp only [castLE_succ_eq r' hle i]; exact hs _)
  show (Matrix.det (Matrix.of fun a b : Fin (l.val + 1 + 1) =>
      star (Y (Fin.castLE hle a)) ⬝ᵥ Y (Fin.castLE hle b))).re = D ^ 2 * Ga k r' l U
  rw [key, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
