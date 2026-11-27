-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.mem_of_isInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:22.347935+00:00
-- url     : https://prove2.me/submissions/3bd853b2-72a3-489c-b8a0-dee05ccfdcee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
private theorem algK_apply_lemma_2 (v : HeightOneSpectrum R) (k : K) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  first
  | rfl
  | (simp; done)
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
theorem _root_.solution (k : K) (h : IsInt (algebraMap K (FiniteAdeleRing R K) k)) :
    k ∈ (algebraMap R K).range := by
  apply mem_integers_of_valuation_le_one
  intro v
  have hv : Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1 := by
    rw [← algK_apply_lemma_2 v k]
    exact h v
  first
  | exact (valuedAdicCompletion_eq_valuation' (R := R) v k).symm.trans_le hv
  | exact (valuedAdicCompletion_eq_valuation' v k).symm.trans_le hv
  | (rw [← valuedAdicCompletion_eq_valuation' (R := R) v k]; exact hv)
end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
