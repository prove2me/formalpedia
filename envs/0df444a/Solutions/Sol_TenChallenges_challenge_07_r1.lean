-- Prove2me | solution 1 for TenChallenges.challenge_07_r1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:11:22.286567+00:00
-- url     : https://prove2.me/submissions/4e2bd1ef-d2a4-44ee-9558-fff7c3537290

import Definitions.Def_TenChallenges_Challenge_07

open MeasureTheory Metric Filter
open scoped ENNReal
open TenChallenges

noncomputable section

private lemma upperDensity_le_one {d : ℕ} (C : PointSet d) : upperDensity C ≤ 1 := by
  unfold upperDensity
  refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun R => ?_)
  apply ENNReal.div_le_of_le_mul
  simpa only [one_mul] using
    (measure_mono (Set.inter_subset_right :
      ((⋃ x ∈ C, ball x 1) ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) ⊆ ball 0 R))

private lemma spherePackingConstant_le_one (d : ℕ) : spherePackingConstant d ≤ 1 := by
  unfold spherePackingConstant
  exact iSup_le fun C => iSup_le fun _ => upperDensity_le_one C

private lemma latticePackingConstant_le_spherePackingConstant (d : ℕ) :
    latticePackingConstant d ≤ spherePackingConstant d := by
  unfold latticePackingConstant spherePackingConstant
  refine iSup_le fun L => iSup_le fun hL => iSup_le fun _ => ?_
  exact le_iSup_of_le (L : PointSet d) (le_iSup_of_le hL le_rfl)

private lemma dist_fin_one (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y = |x 0 - y 0| := by
  simp [EuclideanSpace.dist_eq, Real.dist_eq, Real.sqrt_sq_eq_abs]

theorem solution : statement_07 1 := by
  let v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 2
  let L : AddSubgroup (EuclideanSpace ℝ (Fin 1)) := AddSubgroup.zmultiples v
  let U : Set (EuclideanSpace ℝ (Fin 1)) := ⋃ x ∈ (L : PointSet 1), ball x 1
  let g : ℤ → EuclideanSpace ℝ (Fin 1) := fun k =>
    EuclideanSpace.single 0 (2 * (k : ℝ) + 1)
  let holes : Set (EuclideanSpace ℝ (Fin 1)) := Set.range g

  have hv (k : ℤ) : (k • v) 0 = (k : ℝ) * 2 := by
    simp [v, zsmul_eq_mul]

  have hpacking : IsUnitPacking (L : PointSet 1) := by
    intro x hx y hy hxy
    change x ∈ AddSubgroup.zmultiples v at hx
    change y ∈ AddSubgroup.zmultiples v at hy
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hxy rfl
    have hone : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkl)
    rw [dist_fin_one, hv, hv]
    calc
      2 = 1 * |(2 : ℝ)| := by norm_num
      _ ≤ |(k : ℝ) - (l : ℝ)| * |2| :=
        mul_le_mul_of_nonneg_right hone (abs_nonneg _)
      _ = |(k : ℝ) * 2 - (l : ℝ) * 2| := by
        rw [← abs_mul]
        congr 1
        ring

  have hspan : Submodule.span ℝ (L : PointSet 1) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = (x 0 / 2) • v := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [v]
    rw [hx]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    change v ∈ AddSubgroup.zmultiples v
    exact ⟨1, by simp⟩

  have hcov (x : EuclideanSpace ℝ (Fin 1)) : x ∈ U ∨ x ∈ holes := by
    let k : ℤ := round (x 0 / 2)
    have hkL : k • v ∈ (L : PointSet 1) := by
      change k • v ∈ AddSubgroup.zmultiples v
      exact ⟨k, rfl⟩
    have hround : |x 0 / 2 - (k : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have habs : |x 0 - (k : ℝ) * 2| = 2 * |x 0 / 2 - (k : ℝ)| := by
      calc
        |x 0 - (k : ℝ) * 2| = |2 * (x 0 / 2 - (k : ℝ))| := by congr 1; ring
        _ = 2 * |x 0 / 2 - (k : ℝ)| := by rw [abs_mul]; norm_num
    have hdist : dist x (k • v) ≤ 1 := by
      rw [dist_fin_one, hv, habs]
      linarith
    rcases hdist.lt_or_eq with hlt | heq
    · left
      simp only [U, Set.mem_iUnion]
      exact ⟨k • v, hkL, hlt⟩
    · right
      have hdabs : |x 0 - (k : ℝ) * 2| = 1 := by
        rw [dist_fin_one, hv] at heq
        exact heq
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hdabs with hpos | hneg
      · change x ∈ Set.range g
        refine ⟨k, ?_⟩
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [g]
        linarith
      · change x ∈ Set.range g
        refine ⟨k - 1, ?_⟩
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [g]
        linarith

  have hholes : volume holes = 0 := by
    simpa [holes] using (Set.countable_range g).measure_zero volume

  have hmeasure (R : ℝ) :
      volume (U ∩ ball (0 : EuclideanSpace ℝ (Fin 1)) R) =
        volume (ball (0 : EuclideanSpace ℝ (Fin 1)) R) := by
    apply le_antisymm (measure_mono Set.inter_subset_right)
    rw [← measure_sdiff_null hholes]
    apply measure_mono
    intro x hx
    exact ⟨(hcov x).resolve_right hx.2, hx.1⟩

  have hdensity : upperDensity (L : PointSet 1) = 1 := by
    unfold upperDensity
    change limsup (fun R : ℝ =>
      volume (U ∩ ball (0 : EuclideanSpace ℝ (Fin 1)) R) /
        volume (ball (0 : EuclideanSpace ℝ (Fin 1)) R)) atTop = 1
    calc
      _ = limsup (fun _ : ℝ => (1 : ℝ≥0∞)) atTop := by
        apply limsup_congr
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        rw [hmeasure R]
        exact ENNReal.div_self
          (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 1)) hR).ne'
          measure_ball_ne_top
      _ = 1 := limsup_const 1

  apply le_antisymm
  · exact (spherePackingConstant_le_one 1).trans <| by
      calc
        (1 : ℝ≥0∞) = upperDensity (L : PointSet 1) := hdensity.symm
        _ ≤ latticePackingConstant 1 :=
          le_iSup_of_le L (le_iSup_of_le hpacking (le_iSup_of_le hspan le_rfl))
  · exact latticePackingConstant_le_spherePackingConstant 1
