-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.T_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:38.362969+00:00
-- url     : https://prove2.me/submissions/50c5c71e-55a6-41cd-9930-ff3fcc6e3495

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_eb_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_hF_per
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_hF_qp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_T_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_four_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee hef
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (he : ∀ i, e i ∈ lat Y.b) (hf : ∀ j, f j ∈ lat Y.b) (q : ℕ) (hq : 1 ≤ q) :
    Function.Injective (T Y e q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hT
  have hall : ∀ m : Fin (Fintype.card ι) → ℤ, (∀ l, 0 ≤ m l ∧ m l < q) →
      DimB.Av (DimB.Pm (hF Y e q F.1) m) 0 = 0 := by
    intro m hm
    set r : Fin (Fintype.card ι) → Fin q := fun l => ⟨(m l).toNat, by have := hm l; omega⟩
    have hm' : (fun l => ((r l : ℕ) : ℤ)) = m := by
      funext l; simp only [r]; have := hm l; omega
    have := congrFun hT r
    rw [T_apply, hm', Pi.zero_apply] at this
    exact this
  have h0 := DimB.four_zero (by omega : 0 < q) (hF Y e q F.1) (hF_diff Y e q F.1 F.2.1)
    (hF_per Y e hee he q F.1 F.2) (tau e f hee hef) _ (hF_qp Y e f hee hef hf q F.1 F.2) hall
  apply Subtype.ext
  funext v
  have hv : v = Phi e (fun i => (eb e f hee hef).repr v i) := by
    rw [Phi]
    conv_lhs => rw [← (eb e f hee hef).sum_repr v]
    simp [eb_apply]
  have := congrFun h0 (fun i => (eb e f hee hef).repr v i)
  simp only [hF, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  rw [hv, this]; rfl
end ReciprocityTheory.ChartRestriction.G.I2.DimC
