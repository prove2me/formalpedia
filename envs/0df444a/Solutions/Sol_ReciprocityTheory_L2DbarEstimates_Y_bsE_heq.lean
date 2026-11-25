-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_heq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:41.600807+00:00
-- url     : https://prove2.me/submissions/0e053ac2-8492-42a7-b424-eec0bacfb94b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_ext_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_alg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_nsq_prod
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_sqn_ratio
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_exp_neg_frameWeight_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (h : A.Mset w0 s De → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖h x‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by
  obtain ⟨ha, hnσ, hZ, hSw, hd⟩ := bsD_pos A hD hF hσ hX x x.2
  have e1 := bsC_nsq_prod A mu0 L (T' - 1) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) σ w0 (h x) x
    (by simp only [bsH]; rw [bsE_ext_mem h x.2])
  have e2 := bsC_sqn_ratio A L s w0 x x.2.1
  have e3 := bsC_sqn_ratio A L w w0 x x.2.1
  have e4 := exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw
  have hs0 : 0 ≤ A.sqn L s x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x
  have hw0 : 0 ≤ A.sqn L w x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x
  have hp : 0 ≤ A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x :=
    mul_nonneg (bsA_nsq_nonneg A _ _ x)
      (mul_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg hw0 _))
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  have hc : ((T' - 1 : ℕ) : ℝ) - 1 / 2 = (T' : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hT]; push_cast; ring
  unfold bsW
  rw [e1, e2, e3, e4, ← hc, ← mul_assoc]
  exact bsC_alg _ _ _ _ _ _ (T' - 1) ha hZ hSw
end ReciprocityTheory.L2DbarEstimates.Y
