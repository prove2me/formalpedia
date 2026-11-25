-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.map_PhiL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:11.227277+00:00
-- url     : https://prove2.me/submissions/ee6b5d0e-7f91-4f84-931c-7b02f0212648

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_one
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_norm_Phi
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_PhiL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) :
    Measure.map (PhiL (A := A) (B := B) U) volume = volume := by
  set L := PhiL (A := A) (B := B) U
  set S : Set (Sg ι A B → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 ≤ 1}
  have hU3 : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  have himg : L '' S = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [S, Set.mem_setOf_eq, L, PhiL_apply, norm_Phi U hU1] at hw ⊢
      exact hw
    · intro hz
      refine ⟨Phi (star U) z, ?_, ?_⟩
      · simp only [S, Set.mem_setOf_eq, norm_Phi (star U) hU3]
        exact hz
      · simp only [L, PhiL_apply, ← Phi_mul, hU2, Phi_one]
  have hpos : 0 < volume S := by
    have hopen : IsOpen {z : Sg ι A B → ℂ | ∑ s, ‖z s‖ ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨0, by simp⟩) (measure_mono fun z hz => show ∑ s, ‖z s‖ ^ 2 ≤ 1 from le_of_lt hz)
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Sg ι A B → ℂ)) (r := 1)).ne
      (measure_mono fun z hz => ?_)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    have h1 : ‖z s‖ ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (f := fun s => ‖z s‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ s)) hz
    nlinarith [norm_nonneg (z s)]
  have hdet : |LinearMap.det L| = 1 := by
    have h := Measure.addHaar_image_linearMap (volume : Measure (Sg ι A B → ℂ)) L S
    rw [himg] at h
    have h' : ENNReal.ofReal |LinearMap.det L| * volume S = 1 * volume S := by rw [← h, one_mul]
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact (ENNReal.ofReal_eq_one).1 this
  have hne : LinearMap.det L ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
