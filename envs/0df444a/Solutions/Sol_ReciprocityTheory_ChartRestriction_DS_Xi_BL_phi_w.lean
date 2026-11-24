-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:35.950884+00:00
-- url     : https://prove2.me/submissions/5d34a497-e519-48c4-9558-ac0a31a4f605

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_wp_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have ha := a.isLt
  unfold phiV
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro he
    have := congrArg Fin.val he
    simp only [esI] at this
    omega
  · simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
    rw [if_neg, if_neg]
    · simp
    · intro he
      have := congrArg Fin.val he
      simp [wI, Fin.val_last] at this <;> omega
    · intro he
      have := congrArg Fin.val he
      simp [wI] at this <;> omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
