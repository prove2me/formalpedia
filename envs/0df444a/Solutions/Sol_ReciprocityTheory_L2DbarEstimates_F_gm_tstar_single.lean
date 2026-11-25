-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_tstar_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:36:42.865125+00:00
-- url     : https://prove2.me/submissions/fc00e731-e528-48a7-a4f4-42f376d2722f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section helpers
variable {M : Type*} [TopologicalSpace M]
end helpers
section forms
variable {M : Type*} [TopologicalSpace M]
end forms
section meas
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
end meas
section maps
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
private lemma d_conj_eq_conj_db {n : ℕ} {z : M → V n} (φ : M → ℂ) (j : Fin n) (x : M) :
    d n z j (fun y => conj (φ y)) x = conj (db n z j φ x) := by
  unfold d db
  split_ifs with h
  · set e := Classical.choose h with he_def
    have hc : (fun y => conj (φ y)) ∘ e.symm = Complex.conjCLE ∘ (φ ∘ e.symm) := by
      funext w
      simp
    simp only [wd, wdb]
    rw [hc, Complex.conjCLE.comp_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
    ring
  · simp
end maps
section loc
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
end loc
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (ph : M → ℝ) (φ : M → ℂ) (j : Fin n) (x : M) :
    tstar n z ph ph (gmSingle ph φ j) x = -((Real.exp (ph x) : ℂ) * conj (db n z j φ x)) := by
  have hfun : ∀ k, (fun y => (Real.exp (-ph y) : ℂ) * gmSingle ph φ j y k) =
      fun y => if k = j then conj (φ y) else 0 := by
    intro k
    funext y
    by_cases hk : k = j
    · subst hk
      have hE : (Real.exp (-ph y) : ℂ) * (Real.exp (ph y) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
      simp only [gmSingle, EuclideanSpace.single_apply, eq_self_iff_true, if_true, ← mul_assoc, hE,
        one_mul]
    · simp [gmSingle, hk]
  have hd : ∀ k, d n z k (fun y => (Real.exp (-ph y) : ℂ) * gmSingle ph φ j y k) x =
      if k = j then conj (db n z j φ x) else 0 := by
    intro k
    rw [hfun k]
    by_cases hk : k = j
    · subst hk
      simp only [eq_self_iff_true, if_true]
      exact d_conj_eq_conj_db φ k x
    · simp only [hk, if_false]
      apply d_eq_zero_of_not_mem_tsupport
      first
        | simp
        | (rw [show (fun _ : M => (0 : ℂ)) = 0 from rfl, tsupport_zero]; simp)
  simp only [tstar, hd, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end ReciprocityTheory.L2DbarEstimates.F
