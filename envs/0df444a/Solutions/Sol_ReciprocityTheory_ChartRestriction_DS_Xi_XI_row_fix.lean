-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.XI.row_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:39.613352+00:00
-- url     : https://prove2.me/submissions/f71b884a-2025-48ba-af79-cfd3a730029d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_H_es

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hm
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have h1 : hᴴ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    have := congrArg (fun M => M *ᵥ bvec (esI k r a)) hU'
    simp only [← Matrix.mulVec_mulVec, (hfix a).2, H_es] at this
    exact this
  have h2 := congrFun h1 j
  simp only [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have h3 := congrArg star h2
  rw [star_star] at h3
  rw [h3]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.Xi.XI
