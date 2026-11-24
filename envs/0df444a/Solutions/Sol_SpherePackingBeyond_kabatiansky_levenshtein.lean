-- Prove2me | solution 1 for SpherePackingBeyond.kabatiansky_levenshtein
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:35:52.425248+00:00
-- url     : https://prove2.me/submissions/1e559928-1f91-4481-9b76-8636e802e39a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking
import Definitions.Def_SpherePackingBeyond_D4
import Definitions.Def_SpherePacking
import Theorems.Thm_LinearProgrammingBound
import Theorems.Thm_LefebvreVariations_cohn_elkies_kabatiansky_levenshtein
set_option autoImplicit false
open scoped BigOperators FourierTransform SchwartzMap
open SpherePackingBeyond MeasureTheory

/-! Reduction of the open milestone `SpherePackingBeyond.kabatiansky_levenshtein`
(`Δ_d ≤ 2^{-(0.599-ε)d}` for all large `d`) to the variation
`LefebvreVariations.cohn_elkies_kabatiansky_levenshtein` (Cohn–Zhao: Cohn–Elkies auxiliary functions
reach the Kabatiansky–Levenshtein exponent), through the platform theorem `LinearProgrammingBound`
(Cohn–Elkies, proved on the platform, open step in its local `Theorems/` file).
* `bridge` (axiom-free): a unit packing of `Def_TenChallenges_SpherePacking` is a `SpherePacking` of
  separation `2` with literally the same density, so `spherePackingConstant d ≤ SpherePackingConstant d`.
* `lp_real`: `LinearProgrammingBound` rewritten in real numbers (`f̂(0) > 0` gives `f ≠ 0`).
`#print axioms solution` shows `the gap axiom` from exactly two sources: the variation (the only open step of
this file) and the imported `LinearProgrammingBound`. NOTE: `Definitions/Def_SpherePacking` is not built in
the shared workspace; this file was checked against private oleans (`scratch_imk/lvsb_run.sh`). -/

open LefebvreVariations

/-- A unit packing (centres at mutual distance `≥ 2`, balls of radius `1`) is a `SpherePacking` of
separation `2` with the same upper density, so `spherePackingConstant d ≤ SpherePackingConstant d`. -/
private lemma bridge (d : ℕ) : spherePackingConstant d ≤ SpherePackingConstant d := by
  unfold spherePackingConstant
  refine iSup₂_le fun C hC => ?_
  let S : SpherePacking d :=
    { centers := C, separation := 2, separation_pos := by norm_num,
      centers_dist := fun x y hxy => hC x.2 y.2 (fun h => hxy (Subtype.ext h)) }
  have hS : upperDensity C = S.upperPackingDensity := by
    unfold upperDensity SpherePacking.upperPackingDensity SpherePacking.densityInsideRadius
      SpherePacking.occupiedBallRegion
    have : (⋃ x ∈ C, Metric.ball x 1) = ⋃ x : S.centers, Metric.ball (x : EuclideanSpace ℝ (Fin d))
        (S.separation / 2) := by
      rw [Set.biUnion_eq_iUnion]; norm_num [S]
    rw [this]
  rw [hS]
  exact le_iSup (fun S : SpherePacking d => S.upperPackingDensity) S

private lemma lp_real {d : ℕ} (hd : 0 < d) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (h1 : ∀ x, (((f x).re : ℝ) : ℂ) = f x) (h2 : ∀ x, (((𝓕 f x).re : ℝ) : ℂ) = 𝓕 f x)
    (h3 : ∀ x, 1 ≤ ‖x‖ → (f x).re ≤ 0) (h4 : ∀ x, 0 ≤ (𝓕 f x).re) (h5 : 0 < (𝓕 f 0).re)
    (B : ℝ) (hB : (f 0).re / (𝓕 f 0).re *
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≤ B) :
    SpherePackingConstant d ≤ ENNReal.ofReal B := by
  have hne : f ≠ 0 := by
    rintro rfl; simp at h5
  have hLP := LinearProgrammingBound hne h1 h2 (fun x hx => h3 x hx) (fun x => h4 x) hd
  refine hLP.trans ?_
  rw [← SchwartzMap.fourier_coe]
  have hv : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) =
      ENNReal.ofReal (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))) := by
    rw [measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  rw [hv]
  change ENNReal.ofReal (f 0).re / ENNReal.ofReal ((𝓕 f) 0).re * _ ≤ _
  rw [← ENNReal.ofReal_div_of_pos h5, ← ENNReal.ofReal_mul' measureReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hB

theorem solution : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      spherePackingConstant d ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(0.599 - ε) * (d : ℝ))) := by
  intro ε hε
  obtain ⟨N, hN⟩ := cohn_elkies_kabatiansky_levenshtein ε hε
  refine ⟨max N 1, fun d hd => ?_⟩
  obtain ⟨f, h1, h2, h3, h4, h5, h6⟩ := hN d (le_of_max_le_left hd)
  exact (bridge d).trans (lp_real (le_of_max_le_right hd) f h1 h2 h3 h4 h5 _ h6)
