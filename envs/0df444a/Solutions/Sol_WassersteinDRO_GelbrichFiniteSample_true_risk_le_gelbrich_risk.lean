-- Prove2me | solution 1 for WassersteinDRO.GelbrichFiniteSample.true_risk_le_gelbrich_risk
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:24:02.290488+00:00
-- url     : https://prove2.me/submissions/e08f97fc-a578-430d-aa2c-a102fd66ceba

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichRisk

open MeasureTheory

open WassersteinDRO.GelbrichFiniteSample in
theorem solution {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) (hP : HasMeanCov P μ Sig)
    (hU : (μ, Sig) ∈ uncertaintySet ε μh Sigh) (ℓ : EuclideanSpace ℝ (Fin m) → EReal) :
    risk P ℓ ≤ gelbrichRisk Ξ ε μh Sigh ℓ := by
  have hmem : P ∈ gelbrichHull Ξ ε μh Sigh := ⟨inferInstance, hPΞ, μ, Sig, hP, hU⟩
  unfold gelbrichRisk
  exact le_iSup₂_of_le (f := fun Q (_ : Q ∈ gelbrichHull Ξ ε μh Sigh) => risk Q ℓ) P hmem le_rfl
