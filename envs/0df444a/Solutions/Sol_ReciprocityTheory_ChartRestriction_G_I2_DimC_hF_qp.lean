-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.hF_qp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:58.936183+00:00
-- url     : https://prove2.me/submissions/84cb2ef7-89d6-43ef-9460-bba4a5805e48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Phi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Phi_tau
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Qf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key

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
theorem _root_.solution (hf : ∀ j, f j ∈ lat Y.b) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hFs : F ∈ Y.Sec q)
    (j : Fin (Fintype.card ι)) (z : Fin (Fintype.card ι) → ℂ) :
    hF Y e q F (z + tau e f hee hef j) =
      (Y.ka (f j) * cexp ((q : ℂ) * Real.pi * Hf (f j) (f j) / 2 -
        (q : ℂ) * Real.pi / 2 * Qf e (tau e f hee hef j) - ∑ l, Lk Y e l * tau e f hee hef j l)) *
      cexp (2 * Real.pi * I * q * z j) * hF Y e q F z := by
  have hmain : ∀ κ Fv a b c d g : ℂ, a + b = c + d + g →
      κ * cexp a * Fv * cexp b = κ * cexp c * cexp d * (Fv * cexp g) := by
    intro κ Fv a b c d g h
    have hb : b = c + d + g - a := by linear_combination h
    rw [hb, Complex.exp_sub, Complex.exp_add, Complex.exp_add]
    field_simp [Complex.exp_ne_zero]
    all_goals ring
  have hPhi : Phi e (z + tau e f hee hef j) = Phi e z + f j := by
    rw [Phi_add, Phi_tau]
  have hsec := hFs.2 (f j) (hf j) (Phi e z)
  have hK := key e f hee hef z j
  have hQ := Qf_add e hee z (tau e f hee hef j)
  have hL : ∑ m, Lk Y e m * (z + tau e f hee hef j) m =
      ∑ m, Lk Y e m * z m + ∑ m, Lk Y e m * tau e f hee hef j m := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [hF]
  rw [hPhi, hsec]
  refine hmain _ _ _ _ _ _ _ ?_
  rw [hK, hQ, hL]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.DimC
