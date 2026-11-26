-- Prove2me | solution 1 for Section5BooleanFrame.tilted_bilinear_sum_absolute_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:26.643446+00:00
-- url     : https://prove2.me/submissions/d4fe880f-e44b-4b03-9aa1-763dd612bb43

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_centered_bilinear_mgf
import Theorems.Thm_Section5FiniteProbability_iid_subexponential_absolute_tail
import Theorems.Thm_Section5FiniteProbability_law_integral
section
set_option autoImplicit false

namespace Section5BooleanFrame

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]





theorem probabilityLaw_integral (w : ι → ℝ) (hw : ∑ i, w i^2=1) (f : (ι → Bool) → ℝ) :
    (∫ x, f x ∂probabilityLaw w hw)=tiltedMean w f :=
  Section5FiniteProbability.law_integral _ _ _ _











end Section5BooleanFrame

end
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
theorem solution (w u v : ι → ℝ) (hw : ∑ i, w i^2=1)
    (hu : ∑ i, u i^2=1) (hv : ∑ i, v i^2=1) (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : J → ι → Bool, if (Fintype.card J : ℝ)*t ≤
      |∑ r, (Section5BooleanFrame.amplitude u (x r)*Section5BooleanFrame.amplitude v (x r)-
        Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y))| then
          ∏ r, Section5BooleanFrame.weight w (x r) else 0) ≤
      2*Real.exp (-(Fintype.card J : ℝ)*min (t^2) t/33554432) := by
  classical
  letI : MeasurableSpace (ι → Bool) := ⊤
  have hmgf : ∀ l : ℝ, |l| *512 ≤ 1/2 →
      (∑ x : ι → Bool, Section5BooleanFrame.weight w x*Real.exp (l*(Section5BooleanFrame.amplitude u x*Section5BooleanFrame.amplitude v x-
        Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y)))) ≤ Real.exp (8388608*l^2) := by
    intro l hl
    have he := Section5BooleanFrame.tilted_centered_bilinear_mgf w u v hw hu hv l hl
    have hnum : 32*l^2*(512 : ℝ)^2=8388608*l^2 := by ring
    rw [hnum] at he
    simpa only [ProbabilityTheory.mgf,Section5BooleanFrame.probabilityLaw_integral,Section5BooleanFrame.tiltedMean] using he
  exact Section5FiniteProbability.iid_subexponential_absolute_tail (J := J) (Section5BooleanFrame.weight w)
    (Section5BooleanFrame.weight_nonneg w) (fun x => Section5BooleanFrame.amplitude u x*Section5BooleanFrame.amplitude v x-
      Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y)) hmgf t ht
