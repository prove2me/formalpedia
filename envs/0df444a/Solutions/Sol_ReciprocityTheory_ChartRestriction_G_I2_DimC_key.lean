-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:57.886262+00:00
-- url     : https://prove2.me/submissions/a697b993-f24b-4c6b-89aa-c87a5225a30b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Phi_tau

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
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee hef
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (z : Fin (Fintype.card ι) → ℂ) (j : Fin (Fintype.card ι)) :
    Hf (Phi e z) (f j) = (∑ i, ∑ l, z i * tau e f hee hef j l * S e i l) + 2 * I * z j := by
  have hS : ∀ i l, (S e i l).im = 0 := fun i l => hee i l
  have hi : ∀ i, Hf (e i) (f j) =
      ∑ l, tau e f hee hef j l * S e i l + 2 * I * (if i = j then 1 else 0) := by
    intro i
    have h1 : Hf (e i) (f j) = ∑ l, (starRingEnd ℂ) (tau e f hee hef j l) * S e i l := by
      conv_lhs => rw [← Phi_tau e f hee hef j]
      simp only [Phi, Hf_sum_r]
      rfl
    have him := hef i j
    rw [h1] at him ⊢
    split_ifs at him ⊢ with hij
    · apply Complex.ext
      · simp [Complex.re_sum, hS]
      · simp [Complex.im_sum, hS] at him ⊢
        linarith
    · apply Complex.ext
      · simp [Complex.re_sum, hS]
      · simp [Complex.im_sum, hS] at him ⊢
        linarith
  simp only [Phi, Hf_sum_l, hi, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b _ hb
      simp [hb]
    · simp
end ReciprocityTheory.ChartRestriction.G.I2.DimC
