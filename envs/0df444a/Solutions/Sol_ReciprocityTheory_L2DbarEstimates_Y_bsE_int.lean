-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:39.948805+00:00
-- url     : https://prove2.me/submissions/ecbd273b-1d8d-4994-8c6e-d7a608388fdb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_heq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsE_meas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_lintegral_flat


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
open Classical
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (hh : Fin n → A.Mset w0 s De → ℂ)
    (hhol : ∀ k, Holo n (flatStein A hD hF).z (hh k)) (k : Fin n)
    (hbd : ∫⁻ x, ENNReal.ofReal ((∑ j, ‖hh j x‖ ^ 2) *
          (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤) :
    ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) (hh k) σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤ := by
  rw [lintegral_flat A hD hF _ (bsE_meas A hD hF hσ hX T' (hh k) (hhol k))]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hbd
  rw [Set.piecewise_eq_of_mem _ _ _ x.2, bsE_heq A hD hF hσ hX T' hT (hh k) x]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖hh k x‖ ^ 2 ≤ ∑ j, ‖hh j x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ k)
  have h2 : 0 ≤ (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^
      (-((T' : ℝ) - 3 / 2)) := Real.rpow_nonneg (by positivity) _
  have h3 := Real.exp_pos (-bsPh0 A w w0 s mu0 σ x)
  gcongr
end ReciprocityTheory.L2DbarEstimates.Y
