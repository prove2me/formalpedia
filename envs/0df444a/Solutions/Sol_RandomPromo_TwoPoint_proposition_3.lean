-- Prove2me | solution 1 for RandomPromo.TwoPoint.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:37:18.09554+00:00
-- url     : https://prove2.me/submissions/ae8f47af-3d07-4964-b5e7-cf1f37656521

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

open RandomPromo.TwoPoint

namespace RPProp3Sol

lemma cdf_eq (w : ℝ →₀ ℝ) (x : ℝ) :
    cdf w x = ∑ p ∈ w.support, (if p ≤ x then w p else 0) := by
  unfold cdf; rw [Finset.sum_filter]

lemma pexp_eq (w : ℝ →₀ ℝ) (x : ℝ) :
    pexp w x = ∑ p ∈ w.support, (if p ≤ x then w p * p else 0) := by
  unfold pexp; rw [Finset.sum_filter]

lemma gain_eq (w : ℝ →₀ ℝ) (v : ℝ) : gain w v = v * cdf w v - pexp w v := by
  rw [cdf_eq, pexp_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold gain
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

lemma total (w : ℝ →₀ ℝ) (hw : IsPriceDist w) : ∑ p ∈ w.support, w p = 1 := by
  simpa [Finsupp.sum] using hw.2

lemma cdf_le_one (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (x : ℝ) : cdf w x ≤ 1 := by
  rw [cdf_eq, ← total w hw]
  refine Finset.sum_le_sum (fun p _ => ?_)
  split_ifs
  · exact le_rfl
  · exact hw.1 p

lemma cdf_mono (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {x y : ℝ} (hxy : x ≤ y) :
    cdf w x ≤ cdf w y := by
  rw [cdf_eq, cdf_eq]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have := hw.1 p
  split_ifs with h1 h2 <;> first | exact le_rfl | linarith

lemma gain_nonneg (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (v : ℝ) : 0 ≤ gain w v := by
  unfold gain
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hw.1 p) (le_max_right _ _))

lemma gain_mono (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {v v' : ℝ} (h : v ≤ v') :
    gain w v ≤ gain w v' := by
  unfold gain
  refine Finset.sum_le_sum (fun p _ => ?_)
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (hw.1 p)

/-- `E[P ; x < P ≤ y] ≤ y * P(x < P ≤ y)`. -/
lemma pexp_diff (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {x y : ℝ} (hxy : x ≤ y) :
    pexp w y - pexp w x ≤ y * (cdf w y - cdf w x) := by
  rw [pexp_eq, pexp_eq, cdf_eq, cdf_eq, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have := hw.1 p
  rcases le_or_gt p x with h1 | h1
  · rw [if_pos h1, if_pos (h1.trans hxy), if_pos h1, if_pos (h1.trans hxy)]; nlinarith
  · rw [if_neg (not_le.2 h1), if_neg (not_le.2 h1)]
    rcases le_or_gt p y with h2 | h2
    · rw [if_pos h2, if_pos h2]; nlinarith
    · rw [if_neg (not_le.2 h2), if_neg (not_le.2 h2)]; nlinarith

/-- `E[P ; t < P ≤ x] ≥ t * P(t < P ≤ x)`. -/
lemma pexp_diff' (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {x y : ℝ} (hxy : x ≤ y) :
    x * (cdf w y - cdf w x) ≤ pexp w y - pexp w x := by
  rw [pexp_eq, pexp_eq, cdf_eq, cdf_eq, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have := hw.1 p
  rcases le_or_gt p x with h1 | h1
  · rw [if_pos h1, if_pos (h1.trans hxy), if_pos h1, if_pos (h1.trans hxy)]; nlinarith
  · rw [if_neg (not_le.2 h1), if_neg (not_le.2 h1)]
    rcases le_or_gt p y with h2 | h2
    · rw [if_pos h2, if_pos h2]; nlinarith
    · rw [if_neg (not_le.2 h2), if_neg (not_le.2 h2)]; nlinarith

lemma condExp_mono (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {t x : ℝ} (htx : t ≤ x)
    (ht : 0 < cdf w t) : condExp w t ≤ condExp w x := by
  unfold condExp
  have hab := cdf_mono w hw htx
  have h1 := pexp_diff' w hw htx
  have h2 : 0 ≤ t * cdf w t - pexp w t := by rw [← gain_eq]; exact gain_nonneg w hw t
  rw [div_le_div_iff₀ ht (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) ht.le, mul_nonneg h2 (sub_nonneg.2 hab)]

lemma thresh_props (w : ℝ →₀ ℝ) (hw : IsPriceDist w) {c v : ℝ} (hc : 0 < c)
    (hv : c < gain w v) : thresh w c ≤ v ∧ 0 < cdf w (thresh w c) := by
  set S := {v' : ℝ | gain w v' ≤ c} with hS
  have hbdd : ∀ v' ∈ S, v' ≤ v := by
    intro v' hv'
    by_contra h
    push Not at h
    have := gain_mono w hw h.le
    simp only [hS, Set.mem_ofPred_eq] at hv'
    linarith
  have hne : S.Nonempty := by
    refine ⟨-∑ p ∈ w.support, |p|, ?_⟩
    simp only [hS, Set.mem_ofPred_eq]
    have : gain w (-∑ p ∈ w.support, |p|) = 0 := by
      unfold gain
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have h1 : |p| ≤ ∑ p ∈ w.support, |p| :=
        Finset.single_le_sum (f := fun p => |p|) (fun _ _ => abs_nonneg _) hp
      have h2 := neg_abs_le p
      rw [max_eq_right (by linarith), mul_zero]
    rw [this]; exact hc.le
  have hBdd : BddAbove S := ⟨v, hbdd⟩
  refine ⟨csSup_le hne hbdd, ?_⟩
  by_contra hneg
  push Not at hneg
  set t := thresh w c with ht
  have hpos : ∀ p ∈ w.support, t < p := by
    intro p hp
    by_contra h
    push Not at h
    have hwp : 0 < w p := lt_of_le_of_ne (hw.1 p) (Ne.symm (Finsupp.mem_support_iff.1 hp))
    have : w p ≤ cdf w t := by
      unfold cdf
      exact Finset.single_le_sum (f := fun p => w p) (fun q _ => hw.1 q)
        (Finset.mem_filter.2 ⟨hp, h⟩)
    linarith
  have hsne : w.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := total w hw
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  set m0 := w.support.min' hsne
  have hm0 : t < m0 := hpos _ (Finset.min'_mem _ _)
  have hmem : (t + m0) / 2 ∈ S := by
    simp only [hS, Set.mem_ofPred_eq]
    have : gain w ((t + m0) / 2) = 0 := by
      unfold gain
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have := Finset.min'_le w.support p hp
      rw [max_eq_right (by linarith), mul_zero]
    rw [this]; exact hc.le
  have : (t + m0) / 2 ≤ t := le_csSup hBdd hmem
  linarith

/-- The finite-dimensional bound behind Lemma 6(ii): with `β = F(vL)`, `q = E[P | P ≤ vL]`. -/
lemma key_bound (α vL vH cL cH β q X Δ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hcL : 0 < cL)
    (hv : vL < vH) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : cL < β * (vL - q))
    (hH : β * (vH - q) ≤ cH)
    (hX : X ≤ (α + (1 - α) * β) * q + (1 - α) * (1 - β) * vH) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ^ 2 = α * cL / ((1 - α) * (vH - vL))) :
    X ≤ α * vL + (1 - α) * vH - (1 - α) * cL - 2 * (1 - α) * (vH - vL) * Δ ∧
    ((cH - cL) / (vH - vL) ≤ Δ →
      X ≤ α * vL + (1 - α) * vH - (1 - α) * cH - α * cL * ((vH - vL) / (cH - cL))) := by
  have hD : 0 < vH - vL := by linarith
  have hK : 0 < (1 - α) * (vH - vL) := mul_pos (by linarith) hD
  have hΔ' : α * cL = (1 - α) * (vH - vL) * Δ ^ 2 := by
    have h1α : (1 - α) ≠ 0 := (by linarith : (0:ℝ) < 1 - α).ne'
    rw [hΔ]; field_simp
  -- q < vL - cL/β, i.e. β q < β vL - cL
  have hq : β * q < β * vL - cL := by nlinarith
  have hcoef : 0 < α + (1 - α) * β := by nlinarith
  -- multiply X-bound by β
  have hXβ : β * X ≤ (α + (1 - α) * β) * (β * vL - cL) + (1 - α) * (1 - β) * vH * β := by
    have := mul_le_mul_of_nonneg_left hX hβ0.le
    nlinarith [mul_lt_mul_of_pos_left hq hcoef]
  constructor
  · -- β (U1 - X) ≥ (1-α)D(β-Δ)^2 ≥ 0
    have : β * X ≤ β * (α * vL + (1 - α) * vH - (1 - α) * cL - 2 * (1 - α) * (vH - vL) * Δ) := by
      nlinarith [mul_nonneg hK.le (sq_nonneg (β - Δ))]
    exact le_of_mul_le_mul_left this hβ0
  · intro hb
    have hcc : 0 < cH - cL := by
      have : cL < cH := by nlinarith
      linarith
    set b := (cH - cL) / (vH - vL) with hbdef
    have hbD : b * (vH - vL) = cH - cL := by rw [hbdef]; field_simp
    have hbpos : 0 < b := div_pos hcc hD
    have hβb : β * (vH - vL) < cH - cL := by nlinarith
    have hβb' : β < b := by nlinarith
    have hU2 : α * cL * ((vH - vL) / (cH - cL)) = α * cL / b := by
      rw [hbdef]; field_simp
    rw [hU2]
    -- β b (U2 - X) ≥ (b - β) (α cL - (1-α) D β b) ≥ 0
    have hprod : β * b ≤ Δ ^ 2 := by nlinarith
    have h1 : 0 ≤ (b - β) * (α * cL - (1 - α) * (vH - vL) * β * b) := by
      apply mul_nonneg (by linarith)
      rw [hΔ']; nlinarith [mul_le_mul_of_nonneg_left hprod hK.le]
    have : β * b * X ≤ β * b * (α * vL + (1 - α) * vH - (1 - α) * cH - α * cL / b) := by
      have e : β * b * (α * cL / b) = β * α * cL := by field_simp
      rw [mul_sub, e]
      have hcH : cH = b * (vH - vL) + cL := by linarith
      rw [hcH]
      nlinarith [mul_le_mul_of_nonneg_left hXβ hbpos.le]
    exact le_of_mul_le_mul_left this (mul_pos hβ0 hbpos)

lemma part1 (M : Params) (hM : M.Standing) (hΔ : M.ΔR < 1) (w : ℝ →₀ ℝ)
    (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj2 w ≤ (if M.ΔR < M.bnd then M.U1 else M.U2) := by
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  obtain ⟨hgL, hgH⟩ := hF
  obtain ⟨htle, htpos⟩ := thresh_props w hw hcL hgL
  set t := thresh w M.cL
  have hβpos : 0 < cdf w M.vL := lt_of_lt_of_le htpos (cdf_mono w hw htle)
  have hce := condExp_mono w hw htle htpos
  have hAβ := cdf_mono w hw hv.le
  have hA1 := cdf_le_one w hw M.vH
  have hβ1 : cdf w M.vL ≤ 1 := le_trans hAβ hA1
  have hdiff := pexp_diff w hw hv.le
  rw [gain_eq] at hgL hgH
  set β := cdf w M.vL
  set A := cdf w M.vH
  set m := pexp w M.vL
  set E := pexp w M.vH
  set q := condExp w M.vL with hqdef
  have hA0 : 0 < A := lt_of_lt_of_le hβpos hAβ
  have hm : m = β * q := by
    show m = β * (m / β); field_simp
  have hobj : M.obj2 w ≤ M.α * q + (1 - M.α) * E := by
    unfold Params.obj2
    have : A * condExp w M.vH = E := by
      show A * (E / A) = E; field_simp
    rw [mul_assoc, this]
    nlinarith
  have hΔ0 : 0 ≤ M.ΔR := Real.sqrt_nonneg _
  have hΔsq : M.ΔR ^ 2 = M.α * M.cL / ((1 - M.α) * (M.vH - M.vL)) := by
    unfold Params.ΔR
    rw [Real.sq_sqrt]
    exact div_nonneg (mul_nonneg hα0.le hcL.le) (mul_nonneg (by linarith) (by linarith))
  have hk := key_bound M.α M.vL M.vH M.cL M.cH β q (M.obj2 w) M.ΔR hα0 hα1 hcL hv hβpos hβ1
    (by linarith) (by nlinarith)
    (by nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 hA1)
          (show (0:ℝ) ≤ (1 - M.α) * M.vH by nlinarith)]) hΔ0 hΔsq
  split_ifs with h
  · exact hk.1
  · exact hk.2 (not_lt.1 h)

lemma tp (a b x y : ℝ) (f : ℝ → ℝ) :
    ∑ p ∈ (Finsupp.single a x + Finsupp.single b y).support,
      (Finsupp.single a x + Finsupp.single b y) p * f p = x * f a + y * f b := by
  change Finsupp.sum _ (fun p m => m * f p) = _
  rw [Finsupp.sum_add_index' (by simp) (by intros; ring), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp)]

lemma tp_cdf (a b x y z : ℝ) :
    cdf (Finsupp.single a x + Finsupp.single b y) z =
      x * (if a ≤ z then 1 else 0) + y * (if b ≤ z then 1 else 0) := by
  rw [cdf_eq, ← tp a b x y (fun p => if p ≤ z then 1 else 0)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

lemma tp_pexp (a b x y z : ℝ) :
    pexp (Finsupp.single a x + Finsupp.single b y) z =
      x * (if a ≤ z then a else 0) + y * (if b ≤ z then b else 0) := by
  rw [pexp_eq, ← tp a b x y (fun p => if p ≤ z then p else 0)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

lemma tp_gain (a b x y v : ℝ) :
    gain (Finsupp.single a x + Finsupp.single b y) v =
      x * max (v - a) 0 + y * max (v - b) 0 := by
  unfold gain; rw [tp]

lemma tp_dist (a b x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) :
    IsPriceDist (Finsupp.single a x + Finsupp.single b y) := by
  refine ⟨fun p => ?_, ?_⟩
  · simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> linarith
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring), Finsupp.sum_single_index (by simp),
      Finsupp.sum_single_index (by simp), hxy]

/-- The perturbation `η(δ) = δ (vH - vL)/bnd`. -/
noncomputable def etaFn (M : Params) (δ : ℝ) : ℝ := δ * ((M.vH - M.vL) / M.bnd)

lemma part2_point (M : Params) (hM : M.Standing) (hc : M.cL < M.cH) (hΔ : M.ΔR < 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < M.bnd) :
    IsPriceDist (M.twoPoint δ (etaFn M δ)) ∧ M.Feas (M.twoPoint δ (etaFn M δ)) ∧
    M.obj2 (M.twoPoint δ (etaFn M δ)) =
      M.α * M.pstar δ (etaFn M δ) + (1 - M.α) * (M.βstar δ * M.pstar δ (etaFn M δ) +
        (1 - M.βstar δ) * M.vH) := by
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  have hD : 0 < M.vH - M.vL := by linarith
  have hbpos : 0 < M.bnd := div_pos (by linarith) hD
  have hbD : M.bnd * (M.vH - M.vL) = M.cH - M.cL := by unfold Params.bnd; field_simp
  have hΔpos : 0 < M.ΔR := by
    unfold Params.ΔR
    exact Real.sqrt_pos.2 (div_pos (mul_pos hα0 hcL) (mul_pos (by linarith) hD))
  set β := M.βstar δ with hβdef
  set η := etaFn M δ with hηdef
  have hβle : β ≤ M.bnd - δ := min_le_right _ _
  have hβΔ : β ≤ M.ΔR := min_le_left _ _
  have hβ0 : 0 < β := lt_min hΔpos (by linarith)
  have hβ1 : β < 1 := lt_of_le_of_lt hβΔ hΔ
  have hη0 : 0 < η := mul_pos hδ0 (div_pos hD hbpos)
  have hηb : η * M.bnd = δ * (M.vH - M.vL) := by
    rw [hηdef]; unfold etaFn; field_simp
  set a := M.pstar δ η with hadef
  have ha : a = M.vL - M.cL / β - η := rfl
  have hcβ : 0 < M.cL / β := div_pos hcL hβ0
  have haβ : β * a = β * M.vL - M.cL - β * η := by rw [ha]; field_simp
  have hw : M.twoPoint δ η = Finsupp.single a β + Finsupp.single M.vH (1 - β) := rfl
  rw [hw]
  refine ⟨tp_dist _ _ _ _ hβ0.le (by linarith) (by ring), ⟨?_, ?_⟩, ?_⟩
  · rw [tp_gain, max_eq_left (by linarith), max_eq_right (by linarith)]
    nlinarith [mul_pos hβ0 hη0]
  · rw [tp_gain, max_eq_left (by linarith), max_eq_right (by linarith)]
    -- β (vH - a) = β (vH - vL) + cL + β η ≤ cH
    have h1 : β * (M.vH - M.vL + η) ≤ M.cH - M.cL := by
      have h2 : β * (M.vH - M.vL + η) ≤ (M.bnd - δ) * (M.vH - M.vL + η) :=
        mul_le_mul_of_nonneg_right hβle (by linarith)
      have h3 : (M.bnd - δ) * (M.vH - M.vL + η) * M.bnd ≤ (M.cH - M.cL) * M.bnd := by
        nlinarith [mul_pos hδ0 hδ0, mul_pos (mul_pos hδ0 hδ0) hD]
      have h4 := le_of_mul_le_mul_right h3 hbpos
      linarith
    nlinarith
  · -- the threshold is vL - η
    have hth : thresh (Finsupp.single a β + Finsupp.single M.vH (1 - β)) M.cL = M.vL - η := by
      apply IsGreatest.csSup_eq
      constructor
      · simp only [Set.mem_ofPred_eq]
        rw [tp_gain, max_eq_left (by linarith), max_eq_right (by linarith)]
        nlinarith
      · intro v hv'
        simp only [Set.mem_ofPred_eq] at hv'
        rw [tp_gain] at hv'
        by_contra hlt
        push Not at hlt
        have e1 : β * max (v - a) 0 ≥ β * (v - a) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0.le
        have e2 : 0 ≤ (1 - β) * max (v - M.vH) 0 :=
          mul_nonneg (by linarith) (le_max_right _ _)
        nlinarith
    unfold Params.obj2 condExp
    rw [hth, tp_cdf, tp_cdf, tp_pexp, tp_pexp, if_pos (by linarith), if_neg (by linarith),
      if_pos (by linarith), if_neg (by linarith), if_pos (by linarith), if_pos le_rfl,
      if_pos (by linarith), if_pos le_rfl]
    have hβne := hβ0.ne'
    simp only [mul_one, mul_zero, add_zero]
    rw [mul_div_cancel_left₀ a hβne, show β + (1 - β) = (1:ℝ) by ring, div_one, mul_one]

end RPProp3Sol

open RPProp3Sol in
theorem solution (M : Params) (hM : M.Standing) (hc : M.cL < M.cH) (hΔ : M.ΔR < 1) :
    (∀ w : ℝ →₀ ℝ, IsPriceDist w → M.Feas w →
        M.obj2 w ≤ (if M.ΔR < M.bnd then M.U1 else M.U2)) ∧
    ∃ η : ℝ → ℝ, Filter.Tendsto η (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
        IsPriceDist (M.twoPoint δ (η δ)) ∧ M.Feas (M.twoPoint δ (η δ))) ∧
      Filter.Tendsto (fun δ => M.obj2 (M.twoPoint δ (η δ))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (if M.ΔR < M.bnd then M.U1 else M.U2)) := by
  refine ⟨fun w hw hF => part1 M hM hΔ w hw hF, etaFn M, ?_, ?_, ?_⟩
  · have : Continuous (etaFn M) := by unfold etaFn; fun_prop
    have h := this.tendsto 0
    simp only [etaFn, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · have hM' := hM
    obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM'
    have hbpos : 0 < M.bnd := div_pos (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsGT hbpos] with δ hδ
    obtain ⟨h1, h2, -⟩ := part2_point M hM hc hΔ δ hδ.1 hδ.2
    exact ⟨h1, h2⟩
  · have hM' := hM
    obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM'
    have hD : 0 < M.vH - M.vL := by linarith
    have hbpos : 0 < M.bnd := div_pos (by linarith) hD
    have hΔpos : 0 < M.ΔR := by
      unfold Params.ΔR
      exact Real.sqrt_pos.2 (div_pos (mul_pos hα0 hcL) (mul_pos (by linarith) hD))
    set G : ℝ → ℝ := fun δ => M.α * M.pstar δ (etaFn M δ) + (1 - M.α) *
      (M.βstar δ * M.pstar δ (etaFn M δ) + (1 - M.βstar δ) * M.vH) with hG
    have heq : G =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun δ => M.obj2 (M.twoPoint δ (etaFn M δ))) := by
      filter_upwards [Ioo_mem_nhdsGT hbpos] with δ hδ
      exact (part2_point M hM hc hΔ δ hδ.1 hδ.2).2.2.symm
    refine Filter.Tendsto.congr' heq ?_
    have hβ0 : M.βstar 0 = min M.ΔR M.bnd := by unfold Params.βstar; rw [sub_zero]
    have hβ0pos : 0 < min M.ΔR M.bnd := lt_min hΔpos hbpos
    have hcont : ContinuousAt G 0 := by
      have hb : Continuous (fun δ : ℝ => M.βstar δ) := by unfold Params.βstar; fun_prop
      have he : Continuous (etaFn M) := by unfold etaFn; fun_prop
      have hp : ContinuousAt (fun δ : ℝ => M.pstar δ (etaFn M δ)) 0 := by
        unfold Params.pstar
        refine (continuousAt_const.sub (continuousAt_const.div hb.continuousAt ?_)).sub
          he.continuousAt
        rw [hβ0]; exact hβ0pos.ne'
      rw [hG]
      exact (continuousAt_const.mul hp).add (continuousAt_const.mul
        ((hb.continuousAt.mul hp).add ((continuousAt_const.sub hb.continuousAt).mul
          continuousAt_const)))
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    convert hlim using 2
    have hp0 : M.pstar 0 (etaFn M 0) = M.vL - M.cL / min M.ΔR M.bnd := by
      unfold Params.pstar etaFn; rw [hβ0]; ring
    have hΔsq : M.ΔR ^ 2 = M.α * M.cL / ((1 - M.α) * (M.vH - M.vL)) := by
      unfold Params.ΔR
      rw [Real.sq_sqrt]
      exact div_nonneg (mul_nonneg hα0.le hcL.le) (mul_nonneg (by linarith) (by linarith))
    have h1α : (1 - M.α) ≠ 0 := (by linarith : (0:ℝ) < 1 - M.α).ne'
    have hDne : M.vH - M.vL ≠ 0 := hD.ne'
    rw [hG]
    simp only
    rw [hp0, hβ0]
    split_ifs with h
    · rw [min_eq_left h.le]
      unfold Params.U1
      have hΔ' : M.α * M.cL = (1 - M.α) * (M.vH - M.vL) * M.ΔR ^ 2 := by
        rw [hΔsq]; field_simp
      have hne := hΔpos.ne'
      field_simp
      linear_combination hΔ'
    · rw [min_eq_right (not_lt.1 h)]
      unfold Params.U2
      have hbD : M.bnd * (M.vH - M.vL) = M.cH - M.cL := by unfold Params.bnd; field_simp
      have hcc : M.cH - M.cL ≠ 0 := by
        have := hbpos.ne'; unfold Params.bnd at this; intro h0; rw [h0, zero_div] at this
        exact this rfl
      have hbne := hbpos.ne'
      have hcH' : M.cH = M.bnd * (M.vH - M.vL) + M.cL := by linarith
      rw [hcH']
      field_simp
      ring
