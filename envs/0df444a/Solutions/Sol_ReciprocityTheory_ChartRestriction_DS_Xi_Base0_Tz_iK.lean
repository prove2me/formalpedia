-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.Tz_iK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:55:10.574848+00:00
-- url     : https://prove2.me/submissions/90aa27ad-5cc4-47de-bbba-e61e406ba11b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
private lemma mulVec_bvec_eq_fun_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  first
  | simp [Matrix.mulVec, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, Matrix.dotProduct, bvec, Pi.single_apply]
private lemma star_bvec_dotProduct_eq_apply {n : ℕ} (j : Fin n) (w : Fin n → ℂ) : star (bvec j) ⬝ᵥ w = w j := by
  first
  | (rw [dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | (rw [Matrix.dotProduct, Finset.sum_eq_single j]
     · simp [bvec]
     · intro b _ hb; simp [bvec, Pi.single_apply, hb]
     · simp)
  | simp [bvec]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (k : ℕ) : 0 < Tz k 0 (bvec (iK k)) := by
  have hKK : Hpk k 0 (iK k) (iK k) = -1 := by
    simp [Hpk, iK, wI]
  have hh : herm (Hpk k 0) (bvec (iK k)) (bvec (iK k)) = -1 := by
    unfold herm
    rw [mulVec_bvec_eq_fun_apply, star_bvec_dotProduct_eq_apply]
    exact hKK
  unfold Tz
  rw [hh]
  norm_num
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
