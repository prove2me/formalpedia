-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.phiV_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:10.25449+00:00
-- url     : https://prove2.me/submissions/938f3c1f-83eb-4964-8c41-dde2d5343e40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  unfold phiV
  by_cases hb : (b : ℕ) < r
  · rw [dif_pos hb, if_pos hb]
    show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _
    rw [Pi.single_apply]
    by_cases hi : (i : ℕ) = 2 * r + k - b.val
    · rw [if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]
    · rw [if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]
  · rw [dif_neg hb, if_neg hb]
    simp [epsV, bvec, Pi.single_apply, Fin.ext_iff]
    have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]
    have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]
    rw [e1, e2]
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
