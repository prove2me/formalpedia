-- Prove2me | solution 1 for RiemannMasullo.inTorsionSector_real
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:49:52.219212+00:00
-- url     : https://prove2.me/submissions/8b8af18a-b19e-4d5e-8f01-329b60c57a0e

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L250-L252
import Mathlib
import Definitions.Def_RiemannMasullo_TorsionSector
open RiemannMasullo
open NumberField InfinitePlace.Completion
variable (F : Type*) [Field F] [NumberField F]
variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

theorem solution (hv : v₀.IsReal) (x : v₀.Completionˣ) :
    inTorsionSector F v₀ σ x ↔ 0 < extensionEmbeddingOfIsReal hv x.val := by
  let r := extensionEmbeddingOfIsReal hv x.val
  have hr : r ≠ 0 := (map_ne_zero (extensionEmbeddingOfIsReal hv)).mpr x.ne_zero
  have hfix : σ (extensionEmbedding v₀ x.val) = (r : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hv]
    exact σ.commutes r
  have hp := Units.torsionOrder_pos F
  obtain ⟨k, hk⟩ := Units.even_torsionOrder F
  have htwo : (2 : ℝ) ≤ Units.torsionOrder F := by
    exact_mod_cast (show 2 ≤ Units.torsionOrder F by omega)
  have hp' : (0 : ℝ) < Units.torsionOrder F := by exact_mod_cast hp
  unfold inTorsionSector
  rw [hfix]
  change _ ↔ 0 < r
  rcases lt_or_gt_of_ne hr with hn | hpos
  · rw [Complex.arg_ofReal_of_neg hn]
    have he : 2 * Real.pi / Units.torsionOrder F ≤ Real.pi := by
      apply (div_le_iff₀ hp').mpr
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr htwo)]
    exact ⟨fun h ↦ False.elim ((not_lt_of_ge he) h.2), fun h ↦ False.elim (hn.not_gt h)⟩
  · rw [Complex.arg_ofReal_of_nonneg hpos.le]
    exact ⟨fun _ ↦ hpos, fun _ ↦ ⟨le_rfl, div_pos (by positivity) hp'⟩⟩
