-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P15.sittingPath_concatenate
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T23:46:09.271496+00:00
-- url     : https://prove2.me/submissions/fd4b474b-c3de-4780-a354-6849e9271e8c

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff
open Diffeology Set

universe u

theorem AuxSP_concat_lt {X : Type u} (gammaTwo gammaOne : ℝ → X) {t : ℝ} (ht : t < 1 / 2) :
    sittingPathConcat gammaTwo gammaOne t = gammaOne (2 * t) :=
  if_pos ht

theorem AuxSP_concat_ge {X : Type u} (gammaTwo gammaOne : ℝ → X) {t : ℝ} (ht : ¬ t < 1 / 2) :
    sittingPathConcat gammaTwo gammaOne t = gammaTwo (2 * t - 1) :=
  if_neg ht

theorem AuxSP_concat_zero {X : Type u} (gammaTwo gammaOne : ℝ → X) :
    sittingPathConcat gammaTwo gammaOne 0 = gammaOne 0 := by
  norm_num [sittingPathConcat]

theorem AuxSP_concat_one {X : Type u} (gammaTwo gammaOne : ℝ → X) :
    sittingPathConcat gammaTwo gammaOne 1 = gammaTwo 1 := by
  norm_num [sittingPathConcat]

theorem AuxSP_mid_const {X : Type u}
    {gammaOne gammaTwo : ℝ → X} {eps1 eps2 δ t : ℝ}
    (h1l : ∀ s : ℝ, 1 - eps1 < s → gammaOne s = gammaOne 1)
    (h2z : ∀ s : ℝ, s < eps2 → gammaTwo s = gammaTwo 0)
    (hJoin : gammaOne 1 = gammaTwo 0)
    (hδ1 : 2 * δ ≤ eps1) (hδ2 : 2 * δ ≤ eps2)
    (htl : 1 / 2 - δ < t) (htr : t < 1 / 2 + δ) :
    sittingPathConcat gammaTwo gammaOne t = gammaTwo 0 := by
  by_cases ht : t < 1 / 2
  · rw [AuxSP_concat_lt (gammaTwo := gammaTwo) (gammaOne := gammaOne) ht, hJoin.symm]
    apply h1l
    linarith
  · rw [AuxSP_concat_ge (gammaTwo := gammaTwo) (gammaOne := gammaOne) ht]
    apply h2z
    linarith

theorem AuxSP_dsmooth {X : Type u} [DiffeologicalSpace X]
    {gammaOne gammaTwo : ℝ → X}
    (hOne : IsSittingPath gammaOne) (hTwo : IsSittingPath gammaTwo)
    (hJoin : gammaOne 1 = gammaTwo 0) :
    Diffeology.DSmooth (sittingPathConcat gammaTwo gammaOne) := by
  rcases hOne with ⟨hs1, eps1, he1pos, he1lt, h1z, h1l⟩
  rcases hTwo with ⟨hs2, eps2, he2pos, he2lt, h2z, h2l⟩
  intro n q hq
  have hqC : ContDiff ℝ ∞ q := hq.contDiff
  refine DiffeologicalSpace.locality (p := sittingPathConcat gammaTwo gammaOne ∘ q) ?_
  intro x
  let δ : ℝ := min (eps1 / 2) (eps2 / 2)
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : 2 * δ ≤ eps1 := by
    have : δ ≤ eps1 / 2 := min_le_left _ _
    linarith
  have hδ2 : 2 * δ ≤ eps2 := by
    have : δ ≤ eps2 / 2 := min_le_right _ _
    linarith
  by_cases hxlt : q x < 1 / 2
  · refine ⟨q ⁻¹' Iio (1 / 2), isOpen_Iio.preimage hqC.continuous, hxlt, ?_⟩
    intro m f hfmem hfC
    have hinner : ContDiff ℝ ∞ fun z => (2 : ℝ) * q (f z) :=
      (contDiff_const.mul (hqC.comp hfC))
    have hp : IsPlot (gammaOne ∘ fun z => (2 : ℝ) * q (f z)) :=
      hs1 m _ hinner.isPlot
    have hcomp : (sittingPathConcat gammaTwo gammaOne ∘ q) ∘ f =
        gammaOne ∘ fun z => (2 : ℝ) * q (f z) := by
      ext z
      have hz : q (f z) < 1 / 2 := hfmem z
      simp [Function.comp, AuxSP_concat_lt (gammaTwo := gammaTwo) (gammaOne := gammaOne) hz]
    exact hcomp ▸ hp
  · by_cases hxgt : 1 / 2 < q x
    · refine ⟨q ⁻¹' Ioi (1 / 2), isOpen_Ioi.preimage hqC.continuous, hxgt, ?_⟩
      intro m f hfmem hfC
      have hinner : ContDiff ℝ ∞ fun z => (2 : ℝ) * q (f z) - 1 :=
        (contDiff_const.mul (hqC.comp hfC)).sub contDiff_const
      have hp : IsPlot (gammaTwo ∘ fun z => (2 : ℝ) * q (f z) - 1) :=
        hs2 m _ hinner.isPlot
      have hcomp : (sittingPathConcat gammaTwo gammaOne ∘ q) ∘ f =
          gammaTwo ∘ fun z => (2 : ℝ) * q (f z) - 1 := by
        ext z
        have hz : ¬ q (f z) < 1 / 2 := not_lt_of_gt (hfmem z)
        simp [Function.comp, AuxSP_concat_ge (gammaTwo := gammaTwo) (gammaOne := gammaOne) hz]
      exact hcomp ▸ hp
    · have hxeq : q x = 1 / 2 := le_antisymm (le_of_not_gt hxgt) (le_of_not_gt hxlt)
      refine ⟨q ⁻¹' Ioo (1 / 2 - δ) (1 / 2 + δ),
        isOpen_Ioo.preimage hqC.continuous, ?_, ?_⟩
      · rw [mem_preimage, mem_Ioo, hxeq]
        constructor <;> linarith
      · intro m f hfmem hfC
        have hconst : (sittingPathConcat gammaTwo gammaOne ∘ q) ∘ f =
            fun _ => gammaTwo 0 := by
          ext z
          have hz : q (f z) ∈ Ioo (1 / 2 - δ) (1 / 2 + δ) := hfmem z
          exact AuxSP_mid_const h1l h2z hJoin hδ1 hδ2 hz.1 hz.2
        have hp : IsPlot (fun _ : EuclideanSpace ℝ (Fin m) => gammaTwo 0) :=
          isPlot_const
        exact hconst ▸ hp

theorem _root_.solution
    {X : Type u} [DiffeologicalSpace X]
    (gammaOne gammaTwo : ℝ → X)
    (hOne : IsSittingPath gammaOne) (hTwo : IsSittingPath gammaTwo)
    (hJoin : gammaOne 1 = gammaTwo 0) :
    IsSittingPath (sittingPathConcat gammaTwo gammaOne) := by
  refine ⟨AuxSP_dsmooth hOne hTwo hJoin, ?_⟩
  rcases hOne with ⟨_, eps1, he1pos, he1lt, h1z, h1l⟩
  rcases hTwo with ⟨_, eps2, he2pos, he2lt, h2z, h2l⟩
  refine ⟨min (eps1 / 2) (eps2 / 2), ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · have : min (eps1 / 2) (eps2 / 2) ≤ eps1 / 2 := min_le_left _ _
    linarith
  · intro t ht
    have ht' : t < 1 / 2 := by
      have : min (eps1 / 2) (eps2 / 2) < 1 / 2 := by
        have : eps1 / 2 < 1 / 2 := by linarith
        exact (min_le_left (eps1 / 2) (eps2 / 2)).trans_lt this
      linarith
    rw [AuxSP_concat_lt (gammaTwo := gammaTwo) (gammaOne := gammaOne) ht', AuxSP_concat_zero]
    apply h1z
    have : t < eps1 / 2 := ht.trans_le (min_le_left _ _)
    linarith
  · intro t ht
    have ht' : ¬ t < 1 / 2 := by
      have hmin : min (eps1 / 2) (eps2 / 2) < 1 / 4 :=
        (min_le_left _ _).trans_lt (by linarith : eps1 / 2 < 1 / 4)
      have : (1 / 2 : ℝ) < t := by linarith
      exact not_lt_of_gt this
    rw [AuxSP_concat_ge (gammaTwo := gammaTwo) (gammaOne := gammaOne) ht', AuxSP_concat_one]
    apply h2l
    have : min (eps1 / 2) (eps2 / 2) ≤ eps2 / 2 := min_le_right _ _
    linarith

end QAlgorithms.Papers.Independent.Intake100.P15

end
