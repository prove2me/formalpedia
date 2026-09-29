-- Prove2me | solution 1 for WangZahlKakeya.tube_volume_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T21:05:44.820893+00:00
-- url     : https://prove2.me/submissions/1f60a5e6-5daf-4cd0-b93e-dfd4510b3e39

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

/-! 0a7bc257 WangZahlKakeya.tube_volume_eq.
Route: the reflection `L` in the hyperplane orthogonal to `v - e₀` is a linear isometry with
`L v = e₀` (`reflection_sub`). The map `g x = L (x - p)` is a measure-preserving homeomorphism
(`LinearIsometryEquiv.measurePreserving` after a translation) and `tube p v δ = g ⁻¹' tube 0 e₀ δ`
pointwise, since `dist (L (x - p)) (t • e₀) = dist (x - p) (t • v) = dist x (p + t • v)`. -/

set_option autoImplicit false

open MeasureTheory Metric Set WangZahlKakeya in
theorem solution (p v : E3) (δ : ℝ) (hv : ‖v‖ = 1) :
    (volume (tube p v δ)).toReal = tubeVol δ := by
  set e0 : E3 := EuclideanSpace.single 0 (1 : ℝ) with he0def
  have he0 : ‖e0‖ = 1 := by simp [e0]
  set L : E3 ≃ₗᵢ[ℝ] E3 := Submodule.reflection (ℝ ∙ (v - e0))ᗮ with hLdef
  have hL : L v = e0 := Submodule.reflection_sub (by rw [he0, hv])
  let g : E3 ≃ₜ E3 := (Homeomorph.subRight p).trans L.toHomeomorph
  have hg : MeasurePreserving g volume volume :=
    (L.measurePreserving).comp (measurePreserving_sub_right volume p)
  have hpre : tube p v δ = g ⁻¹' tube 0 e0 δ := by
    ext x
    simp only [tube, mem_iUnion, mem_closedBall, mem_preimage, zero_add, exists_prop]
    refine exists_congr (fun t => and_congr_right (fun _ => ?_))
    have hgx : g x = L (x - p) := rfl
    rw [hgx, ← hL, ← L.map_smul, L.dist_map, dist_eq_norm, dist_eq_norm, sub_sub]
  rw [hpre, hg.measure_preimage_emb g.measurableEmbedding]
  rfl
