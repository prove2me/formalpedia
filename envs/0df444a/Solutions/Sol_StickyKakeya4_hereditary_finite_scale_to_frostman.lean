-- Prove2me | solution 1 for StickyKakeya4.hereditary_finite_scale_to_frostman
-- status  : ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-27T12:40:19.950593+00:00
-- url     : https://prove2.me/submissions/e9efd453-1f51-438c-affe-f2055589c916

import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set
open StickyKakeya4

theorem solution
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    (hsources : HasCoherentFiniteScaleSources selector)
    (huniform : HasUniformMarkedSourceEstimate selector) :
    HasFrontFrostmanMeasures selector := by
  intro ε hε hε4
  obtain ⟨Cpack, hCpack0, hCpackTop, μ, hμprob, hμsupport,
      δs, hδs, hsourcesδ⟩ := hsources ε hε
  obtain ⟨A, hA0, hATop, δu, hδu, huniformδ⟩ :=
    huniform ε hε Cpack hCpack0 hCpackTop
  let δ₀ : ℝ := min δs (min δu (1 / 3 : ℝ))
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀s : δ₀ ≤ δs := min_le_left _ _
  have hδ₀u : δ₀ ≤ δu := le_trans (min_le_right _ _) (min_le_left _ _)
  let κ : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ Fintype.card (Fin 4) /
      Real.Gamma ((Fintype.card (Fin 4) : ℝ) / 2 + 1))
  let Csmall : ENNReal := Cpack * A * (ENNReal.ofReal 3) ^ 4 * κ
  let Clarge : ENNReal :=
    (ENNReal.ofReal δ₀).rpow (-(4 - ε))
  refine ⟨μ, hμprob, hμsupport, Csmall + Clarge, ?_, ?_⟩
  · apply ENNReal.add_ne_top.mpr
    constructor
    · dsimp [Csmall, κ]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top hCpackTop hATop
        · simp
      · exact ENNReal.ofReal_ne_top
    · dsimp [Clarge]
      rw [ENNReal.rpow_neg]
      apply (ENNReal.inv_ne_top).mpr
      exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ₀)
        ENNReal.ofReal_ne_top)
  · intro x r hr hr1
    by_cases hrsmall : r ≤ δ₀
    · obtain ⟨n, D, hDδ, hDselector, hDadmissible,
          hDmassLower, hDmassUpper, hlocal⟩ :=
        hsourcesδ r hr (le_trans hrsmall hδ₀s)
      let R : FiniteScaleSource n := Classical.choose (hlocal x)
      have hRspec := Classical.choose_spec (hlocal x)
      rcases hRspec with ⟨hRrestriction, hRunion, hmball⟩
      have hDδu : D.thickness ≤ δu := by
        rw [hDδ]
        exact le_trans hrsmall hδ₀u
      have hRmass :=
        (huniformδ n D R hDδu hDselector hDadmissible hRrestriction).2
      have htwo_three : 2 * r < 3 * r := by nlinarith
      have hvolume :
          volume (sourceUnion R) ≤
            (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
        calc
          volume (sourceUnion R) ≤ volume (Metric.ball x (3 * r)) :=
            measure_mono (hRunion.trans (Metric.closedBall_subset_ball htwo_three))
          _ = (ENNReal.ofReal (3 * r)) ^ 4 * κ := by
            simpa [κ] using EuclideanSpace.volume_ball (Fin 4) x (3 * r)
      have hrENN0 : ENNReal.ofReal r ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hr)
      have hrpow4 :
          (ENNReal.ofReal r) ^ 4 =
            (ENNReal.ofReal r).rpow (4 : ℝ) :=
        (ENNReal.rpow_natCast (ENNReal.ofReal r) 4).symm
      have hrpowSum :
          (ENNReal.ofReal r).rpow (4 - ε) =
            (ENNReal.ofReal r).rpow (-ε) *
              (ENNReal.ofReal r).rpow (4 : ℝ) := by
        rw [show 4 - ε = -ε + 4 by ring]
        exact ENNReal.rpow_add (-ε) 4 hrENN0 ENNReal.ofReal_ne_top
      have hscale :
          (ENNReal.ofReal r).rpow (-ε) *
              ((ENNReal.ofReal (3 * r)) ^ 4 * κ) =
            ((ENNReal.ofReal 3) ^ 4 * κ) *
              (ENNReal.ofReal r).rpow (4 - ε) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
        calc
          (ENNReal.ofReal r).rpow (-ε) *
                (((ENNReal.ofReal 3) ^ 4 * (ENNReal.ofReal r) ^ 4) * κ) =
              ((ENNReal.ofReal 3) ^ 4 * κ) *
                ((ENNReal.ofReal r).rpow (-ε) * (ENNReal.ofReal r) ^ 4) := by
                  ac_rfl
          _ = ((ENNReal.ofReal 3) ^ 4 * κ) *
                ((ENNReal.ofReal r).rpow (-ε) *
                  (ENNReal.ofReal r).rpow (4 : ℝ)) := by
                  rw [hrpow4]
          _ = ((ENNReal.ofReal 3) ^ 4 * κ) *
                (ENNReal.ofReal r).rpow (4 - ε) := by
                  rw [hrpowSum]
      have hsmall :
          μ (Metric.ball x r) ≤
            Csmall * (ENNReal.ofReal r).rpow (4 - ε) := by
        calc
          μ (Metric.ball x r) ≤ Cpack * sourceMass R := hmball
          _ ≤ Cpack *
                (A * (ENNReal.ofReal D.thickness).rpow (-ε) *
                  volume (sourceUnion R)) := by
              gcongr
          _ = Cpack *
                (A * (ENNReal.ofReal r).rpow (-ε) *
                  volume (sourceUnion R)) := by rw [hDδ]
          _ ≤ Cpack *
                (A * (ENNReal.ofReal r).rpow (-ε) *
                  ((ENNReal.ofReal (3 * r)) ^ 4 * κ)) := by
              gcongr
          _ = Csmall * (ENNReal.ofReal r).rpow (4 - ε) := by
              calc
                Cpack *
                    (A * (ENNReal.ofReal r).rpow (-ε) *
                      ((ENNReal.ofReal (3 * r)) ^ 4 * κ)) =
                    Cpack * A *
                      ((ENNReal.ofReal r).rpow (-ε) *
                        ((ENNReal.ofReal (3 * r)) ^ 4 * κ)) := by
                          ac_rfl
                _ = Cpack * A *
                      (((ENNReal.ofReal 3) ^ 4 * κ) *
                        (ENNReal.ofReal r).rpow (4 - ε)) := by rw [hscale]
                _ = Csmall * (ENNReal.ofReal r).rpow (4 - ε) := by
                      simp only [Csmall]
                      ac_rfl
      calc
        μ (Metric.ball x r) ≤
            Csmall * (ENNReal.ofReal r).rpow (4 - ε) := hsmall
        _ ≤ (Csmall + Clarge) *
            (ENNReal.ofReal r).rpow (4 - ε) := by
          gcongr
          exact le_add_right (le_refl Csmall)
    · have hδ₀r : δ₀ ≤ r := le_of_not_ge hrsmall
      have hexp : 0 < 4 - ε := sub_pos.mpr hε4
      have hpowmono :
          (ENNReal.ofReal δ₀).rpow (4 - ε) ≤
            (ENNReal.ofReal r).rpow (4 - ε) := by
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hδ₀r) hexp.le
      have hbase0 : (ENNReal.ofReal δ₀).rpow (4 - ε) ≠ 0 := by
        exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ₀)
          ENNReal.ofReal_ne_top)
      have hbaseTop : (ENNReal.ofReal δ₀).rpow (4 - ε) ≠ ⊤ := by
        exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hexp.le ENNReal.ofReal_ne_top)
      have hone :
          1 ≤ Clarge * (ENNReal.ofReal r).rpow (4 - ε) := by
        dsimp [Clarge]
        rw [ENNReal.rpow_neg]
        calc
          1 = ((ENNReal.ofReal δ₀).rpow (4 - ε))⁻¹ *
                (ENNReal.ofReal δ₀).rpow (4 - ε) :=
              (ENNReal.inv_mul_cancel hbase0 hbaseTop).symm
          _ ≤ ((ENNReal.ofReal δ₀).rpow (4 - ε))⁻¹ *
                (ENNReal.ofReal r).rpow (4 - ε) := by
              gcongr
      have hprobball : μ (Metric.ball x r) ≤ 1 := by
        calc
          μ (Metric.ball x r) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := hμprob.measure_univ
      calc
        μ (Metric.ball x r) ≤ 1 := hprobball
        _ ≤ Clarge * (ENNReal.ofReal r).rpow (4 - ε) := hone
        _ ≤ (Csmall + Clarge) *
            (ENNReal.ofReal r).rpow (4 - ε) := by
          gcongr
          exact le_add_left (le_refl Clarge)
