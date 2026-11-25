-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_inG_of_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:18.979922+00:00
-- url     : https://prove2.me/submissions/bbca5f91-24ec-4314-8b4c-e4a42d6dfaaf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_hd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_hd_conjT
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {c : ℝ → Matrix (Fin n) (Fin n) ℂ} {c' : Matrix (Fin n) (Fin n) ℂ} {s0 : ℝ}
    (hc : HasDerivAt c c' s0) (hcU : ∀ᶠ s in 𝓝 s0, Formalism.REAL.inUJ ε (c s)) :
    Formalism.REAL.inG ε (slmJi ε (c s0) * c') := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJt := Formalism.REAL.Jm_conjTranspose ε
  have e1 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← mul_assoc, hJ, one_mul]
  have h1 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε) (c'ᴴ * Formalism.REAL.Jm ε) s0 := by
    have := slm_hd_mul (slm_hd_conjT hc) (hasDerivAt_const s0 (Formalism.REAL.Jm ε))
    simpa using this
  have hD : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s)
      (c'ᴴ * Formalism.REAL.Jm ε * c s0 + (c s0)ᴴ * Formalism.REAL.Jm ε * c') s0 := slm_hd_mul h1 hc
  have hD0 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s) 0 s0 := by
    apply (hasDerivAt_const s0 (Formalism.REAL.Jm ε)).congr_of_eventuallyEq
    filter_upwards [hcU] with s hs
    exact hs
  have hsum := hD.unique hD0
  show (slmJi ε (c s0) * c')ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (slmJi ε (c s0) * c') = 0
  unfold slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, mul_assoc, hJ,
    Matrix.mul_one, e1]
  simpa [mul_assoc] using hsum
end ReciprocityTheory.ChartRestriction.DS
