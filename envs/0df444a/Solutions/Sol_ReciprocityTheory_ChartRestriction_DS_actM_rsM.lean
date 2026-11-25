-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.actM_rsM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:40.618323+00:00
-- url     : https://prove2.me/submissions/82ee618e-77e2-4775-a26c-20b4e256a540

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (fun a b => rsM (single a b (1 : ℂ))) X = rsM X := by

  have h1 : ∀ a b, X a b • rsM (single a b (1 : ℂ)) = rsL n (X a b • single a b (1 : ℂ)) :=
    fun a b => rsM_smul _ _
  have h2 : ∑ a, ∑ b, X a b • single a b (1 : ℂ) = X := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp
  unfold actM
  simp only [h1, ← map_sum, h2]
  rfl
end ReciprocityTheory.ChartRestriction.DS
