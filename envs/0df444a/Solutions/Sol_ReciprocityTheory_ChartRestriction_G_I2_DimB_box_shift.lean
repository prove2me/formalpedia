-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.box_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:15.896868+00:00
-- url     : https://prove2.me/submissions/8724b32e-bd8c-4a2a-8968-bbdffb0a06d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_tproj_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_descend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (φ : (Fin k → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin k → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) (s : Fin k → ℝ) :
    ∫ x in ubox k, φ (x + s) = ∫ x in ubox k, φ x := by
  obtain ⟨D, hD⟩ := descend φ hφ hp
  let D' : C(UnitAddTorus (Fin k), ℂ) := ⟨fun θ => D (θ + tproj s), by fun_prop⟩
  have h1 : ∀ x, φ (x + s) = D' (tproj x) := fun x => by
    rw [← hD, tproj_add]; rfl
  have h2 : ∀ x, φ x = D (tproj x) := fun x => (hD x).symm
  have e0 := UnitAddTorus.integral_preimage (fun θ => D θ) 0
  have es := UnitAddTorus.integral_preimage (fun θ => D θ) s
  have m0 : MeasurableSet (ubox k) := by
    have := MeasurableSet.univ_pi (fun i : Fin k =>
      (measurableSet_Ioc : MeasurableSet (Ioc ((0 : Fin k → ℝ) i) ((0 : Fin k → ℝ) i + 1))))
    convert this using 1; ext x; simp [ubox]
  have ms : MeasurableSet {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)} := by
    have := MeasurableSet.univ_pi (fun i : Fin k =>
      (measurableSet_Ioc : MeasurableSet (Ioc (s i) (s i + 1))))
    convert this using 1; ext x; simp
  have key : ∫ x in ubox k, φ (x + s) = ∫ x in {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)}, φ x := by
    rw [← integral_indicator m0, ← integral_indicator ms,
      ← integral_add_right_eq_self (μ := volume)
        (indicator {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)} φ) s]
    congr 1; funext x
    simp only [indicator, ubox, Pi.zero_apply, zero_add, mem_Ioc]
    congr 1
    apply propext
    refine forall_congr' fun i => ?_
    constructor <;> intro h <;> simp only [Pi.add_apply] at h ⊢ <;> constructor <;> linarith [h.1, h.2]
  rw [key]
  simp_rw [h2]
  exact es.symm.trans e0
end ReciprocityTheory.ChartRestriction.G.I2.DimB
