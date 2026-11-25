-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_gradDens_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:53.405854+00:00
-- url     : https://prove2.me/submissions/030d3796-696f-45b6-9cee-431300675b17

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_dz_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_dzb_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (a b c : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (hc : c =ᶠ[𝓝 y] fun z => a z * b z) :
    gradDens φ c b y = a y * gradDens φ b b y + gradDens φ a (fun z => 1 / 2 * (b z * b z)) y := by
  have hLa := ha.hasFDerivAt
  have hLb := hb.hasFDerivAt
  have hc' : HasFDerivAt c (a y • fderiv ℝ b y + b y • fderiv ℝ a y) y :=
    (hLa.mul hLb).congr_of_eventuallyEq hc
  have hbb : HasFDerivAt (fun z => 1 / 2 * (b z * b z))
      ((1 / 2 : ℝ) • (b y • fderiv ℝ b y + b y • fderiv ℝ b y)) y :=
    (hLb.mul hLb).const_mul (1 / 2)
  have e1 : ∀ j, dz j (cplx c) y = (a y : ℂ) * dz j (cplx b) y + (b y : ℂ) * dz j (cplx a) y := by
    intro j
    rw [st_dz_cplx hc', st_dz_cplx hLb, st_dz_cplx hLa]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have e2 : ∀ k, dzb k (cplx (fun z => 1 / 2 * (b z * b z))) y = (b y : ℂ) * dzb k (cplx b) y := by
    intro k
    rw [st_dzb_cplx hbb, st_dzb_cplx hLb]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    push_cast
    ring
  have hmat : gradMat c b y = (a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y := by
    ext j k
    simp only [gradMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e1, e2]
    ring
  simp only [gradDens]
  rw [hmat, mdisc_cons_eq_sum, mdisc_cons_eq_sum, mdisc_cons_eq_sum]
  have hs : ∑ j, ∑ k, ((a y : ℂ) • gradMat b b y + gradMat a (fun z => 1 / 2 * (b z * b z)) y) j k *
        mixedCof (fun i => hessC (φ i) y) j k =
      (a y : ℂ) * ∑ j, ∑ k, gradMat b b y j k * mixedCof (fun i => hessC (φ i) y) j k +
        ∑ j, ∑ k, gradMat a (fun z => 1 / 2 * (b z * b z)) y j k * mixedCof (fun i => hessC (φ i) y) j k := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hs, Complex.add_re, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.AnForm.M
