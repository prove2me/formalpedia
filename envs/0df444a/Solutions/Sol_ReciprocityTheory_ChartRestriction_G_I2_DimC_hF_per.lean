-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.hF_per
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:51.116217+00:00
-- url     : https://prove2.me/submissions/a0e876d8-51be-4246-8c73-087f33ba4524

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Phi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Phi_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_Qf_add

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
include hee
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (he : ∀ i, e i ∈ lat Y.b) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hFs : F ∈ Y.Sec q)
    (l : Fin (Fintype.card ι)) (z : Fin (Fintype.card ι) → ℂ) :
    hF Y e q F (z + Pi.single l 1) = hF Y e q F z := by
  have hmain : ∀ Fv a b c L : ℂ, L + a + b = c → cexp L * cexp a * Fv * cexp b = Fv * cexp c := by
    intro Fv a b c L h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  have hka : Y.ka (e l) = cexp (Lk Y e l) := by
    rw [Lk, Complex.exp_log]
    intro h0
    have h1 := Y.ka_abs (e l) (he l)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hPhi : Phi e (z + Pi.single l 1) = Phi e z + e l := by
    rw [Phi_add, Phi_single]
  have hsec := hFs.2 (e l) (he l) (Phi e z)
  have hX : Hf (Phi e z) (e l) = ∑ i, z i * Hf (e i) (e l) := by
    simp only [Phi, Hf_sum_l]
  have hQs : Qf e (Pi.single l 1) = Hf (e l) (e l) := by
    simp [Qf, S, Pi.single_apply]
  have hsum2 : ∑ i, ∑ m, z i * (Pi.single l (1 : ℂ) : Fin (Fintype.card ι) → ℂ) m * S e i m =
      ∑ i, z i * Hf (e i) (e l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [S, Pi.single_apply]
  have hQ : Qf e (z + Pi.single l 1) = Qf e z + Hf (e l) (e l) + 2 * ∑ i, z i * Hf (e i) (e l) := by
    rw [Qf_add e hee, hQs, hsum2]
  have hL : ∑ m, Lk Y e m * ((z + Pi.single l 1 : Fin (Fintype.card ι) → ℂ) m) = ∑ m, Lk Y e m * z m + Lk Y e l := by
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  simp only [hF]
  rw [hPhi, hsec, hka]
  refine hmain _ _ _ _ _ ?_
  rw [hX, hQ, hL]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.DimC
