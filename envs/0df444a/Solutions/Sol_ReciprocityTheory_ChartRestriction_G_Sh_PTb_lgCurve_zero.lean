-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:55.196005+00:00
-- url     : https://prove2.me/submissions/75d18384-2ab3-4801-91a6-99d6abef27a3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
private theorem hs_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact hasSubst_of_constantCoeff_zero ha0
  | exact HasSubst.of_constantCoeff_zero' ha0
  | exact hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) (a : Fin d) : G.lgCurve 0 a = 0 := by
  classical
  have h0 : HasSubst (0 : Fin d → PowerSeries C) := hs_lemma_2 (fun _ => by simp)
  show subst (0 : Fin d → PowerSeries C) (G.lg a) = 0
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst h0, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · rw [hn, coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext fun s => by simpa using h s)
    have hp : (n.prod fun s k => (0 : Fin d → PowerSeries C) s ^ k) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [Pi.zero_apply, zero_pow hs])
    rw [hp, map_zero, smul_zero]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
