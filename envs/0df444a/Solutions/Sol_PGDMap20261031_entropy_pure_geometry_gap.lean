-- Prove2me | solution 1 for PGDMap20261031.entropy_pure_geometry_gap
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T16:28:11.043561+00:00
-- url     : https://prove2.me/submissions/f56cbd71-5200-4f0d-8edc-2d7628bb9aee

import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_PGDMap20261031_Entropy
import Theorems.Thm_PGDMap20261031_entropy_error_lub
import Theorems.Thm_PGDMap20261031_entropy_unique_optimum

open PGDMap20261031 Set Filter
open scoped Topology BigOperators
noncomputable section

private lemma A0pos (M : EntropyMixture) : 0 < curvatureAtZero M := by
  unfold curvatureAtZero
  exact Finset.sum_pos (fun j _ => mul_pos (M.weight_pos j) (M.a_pos j))
    ⟨⟨0, M.m_pos⟩, Finset.mem_univ _⟩

private lemma E0 (M : EntropyMixture) (c p : ℝ) :
    curvatureError M c p 0 = (p - curvatureAtZero M) / (p + M.lambda) := by
  simp [curvatureError, powerCurvature, mixtureCurvature, entropyCurvature, curvatureAtZero]

private lemma profile_nonneg (M : EntropyMixture) (c p : ℝ) (hv : validGeometry (c, p)) :
    0 ≤ contraction M c p := le_trans (abs_nonneg _)
      ((entropy_error_lub M c p hv).1 ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)

private lemma profile_lsc (M : EntropyMixture) (c a b : ℝ) (hc : 0 ≤ c ∧ c ≤ 2)
    (ha : 0 < a) : LowerSemicontinuousOn (fun p => contraction M c p) (Icc a b) := by
  intro p hp
  apply lowerSemicontinuousWithinAt_iff.mpr
  intro y hy
  have hv : validGeometry (c, p) := ⟨hc.1, hc.2, lt_of_lt_of_le ha hp.1⟩
  obtain ⟨v, ⟨t, ht, rfl⟩, hyt, _⟩ := (entropy_error_lub M c p hv).exists_between hy
  have hk : 0 < powerCurvature c t := by
    unfold powerCurvature
    exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
      (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)
  have hB : 0 < entropyCurvature M t := div_pos M.lambda_pos
    (by nlinarith [ht.1, ht.2])
  have hd : 0 < p * powerCurvature c t + entropyCurvature M t :=
    add_pos (mul_pos hv.2.2 hk) hB
  have hcont : ContinuousAt (fun q : ℝ => |curvatureError M c q t|) p := by
    unfold curvatureError
    exact ((continuousAt_id.mul continuousAt_const |>.sub continuousAt_const).div
      (continuousAt_id.mul continuousAt_const |>.add continuousAt_const)
      (ne_of_gt hd)).abs
  have hevent : ∀ᶠ q in 𝓝 p, y < |curvatureError M c q t| :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds hyt)
  have hevent' : ∀ᶠ q in 𝓝[Icc a b] p, y < |curvatureError M c q t| :=
    hevent.filter_mono nhdsWithin_le_nhds
  filter_upwards [hevent', self_mem_nhdsWithin] with q hq hqK
  exact lt_of_lt_of_le hq ((entropy_error_lub M c q
    ⟨hc.1, hc.2, lt_of_lt_of_le ha hqK.1⟩).1 ⟨t, ht, rfl⟩)

private lemma compact_p (M : EntropyMixture) (c p : ℝ) (hv : validGeometry (c, p))
    (hr : contraction M c p ≤ entropyBaseline M) :
    p ∈ Icc (curvatureAtZero M / 2)
      (curvatureAtZero M * (curvatureAtZero M + 3 * M.lambda) / (2 * M.lambda)) := by
  have hA := A0pos M
  have hl := M.lambda_pos
  have hd : 0 < p + M.lambda := add_pos hv.2.2 hl
  have he := le_trans ((entropy_error_lub M c p hv).1
    ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩) hr
  rw [E0] at he
  obtain ⟨hneg, hpos⟩ := abs_le.mp he
  rw [le_div_iff₀ hd] at hneg
  rw [div_le_iff₀ hd] at hpos
  have hden : 0 < curvatureAtZero M + 2 * M.lambda := by positivity
  dsimp [entropyBaseline] at hneg hpos
  have hneg' := mul_le_mul_of_nonneg_right hneg hden.le
  have hpos' := mul_le_mul_of_nonneg_right hpos hden.le
  field_simp [ne_of_gt hden] at hneg' hpos'
  constructor
  · nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * M.lambda)).2
    nlinarith

private lemma fixed_gap (M : EntropyMixture) (z : ℝ × ℝ) (hz : IsGeometryOptimum M z)
    (c : ℝ) (hc : 0 ≤ c ∧ c ≤ 2) (hcz : c ≠ z.1) :
    contraction M z.1 z.2 < sInf (fixedGeometryValues M c) := by
  have hloc := (entropy_unique_optimum M).2 z hz
  have hA := A0pos M
  have hl := M.lambda_pos
  let a := curvatureAtZero M / 2
  let b := curvatureAtZero M * (curvatureAtZero M + 3 * M.lambda) / (2 * M.lambda)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (le_div_iff₀ (by positivity : 0 < 2 * M.lambda)).2
    nlinarith
  obtain ⟨p, hpK, hpmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (⟨a, le_rfl, hab⟩ : (Icc a b).Nonempty) isCompact_Icc (profile_lsc M c a b hc ha)
  have hp : 0 < p := lt_of_lt_of_le ha hpK.1
  have hv : validGeometry (c, p) := ⟨hc.1, hc.2, hp⟩
  have hstrict : contraction M z.1 z.2 < contraction M c p := by
    have hle := hz.2 (c, p) hv
    by_contra hn
    have heq : contraction M c p = contraction M z.1 z.2 := le_antisymm (le_of_not_gt hn) hle
    have hopt : IsGeometryOptimum M (c, p) := ⟨hv, by
      intro u hu
      simpa only [heq] using hz.2 u hu⟩
    obtain ⟨w, _, hw⟩ := (entropy_unique_optimum M).1
    have hpair : (c, p) = z := (hw (c, p) hopt).trans (hw z hz).symm
    exact hcz (congrArg Prod.fst hpair)
  have hsmall : contraction M z.1 z.2 < entropyBaseline M := hloc.2.2.2.2.2.2.1
  have hbound : min (contraction M c p) (entropyBaseline M) ∈
      lowerBounds (fixedGeometryValues M c) := by
    rintro v ⟨q, hq, rfl⟩
    by_cases hqval : contraction M c q ≤ entropyBaseline M
    · have hqK : q ∈ Icc a b := compact_p M c q ⟨hc.1, hc.2, hq⟩ hqval
      exact le_trans (min_le_left _ _) (hpmin hqK)
    · exact le_trans (min_le_right _ _) (le_of_lt (lt_of_not_ge hqval))
  have hne : (fixedGeometryValues M c).Nonempty :=
    ⟨contraction M c 1, 1, by norm_num, rfl⟩
  have hlow : min (contraction M c p) (entropyBaseline M) ≤
      sInf (fixedGeometryValues M c) := le_csInf hne hbound
  exact lt_of_lt_of_le (lt_min hstrict hsmall) hlow

theorem solution : PureGeometryStrictClaim := by
  intro M z hz
  have hloc := (entropy_unique_optimum M).2 z hz
  constructor
  · exact fixed_gap M z hz 0 ⟨le_rfl, by norm_num⟩ (ne_of_lt hloc.1)
  · apply fixed_gap M z hz 1 ⟨by norm_num, by norm_num⟩
    have : z.1 < 1 := lt_trans hloc.2.1 hloc.2.2.1
    exact ne_of_gt this
