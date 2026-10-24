-- Prove2me | solution 1 for RandomPromo.TwoPoint.lemma_6_ii_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:46:35.979989+00:00
-- url     : https://prove2.me/submissions/7fd6d7d7-d463-43e4-8132-e6400e302e66

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


namespace RPProp3Sol

lemma core (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ)
    (hw : IsPriceDist w) (hF : M.Feas w) :
    condExp w (thresh w M.cL) ≤ condExp w M.vL ∧ M.obj2 w ≤ M.obj3 w ∧
    0 < cdf w M.vL ∧ cdf w M.vL ≤ 1 ∧ M.cL < cdf w M.vL * (M.vL - condExp w M.vL) ∧
    cdf w M.vL * (M.vH - condExp w M.vL) ≤ M.cH ∧
    M.obj3 w ≤ (M.α + (1 - M.α) * cdf w M.vL) * condExp w M.vL +
      (1 - M.α) * (1 - cdf w M.vL) * M.vH := by
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
  have hAE : A * condExp w M.vH = E := by
    show A * (E / A) = E; field_simp
  have h23 : M.obj2 w ≤ M.obj3 w := by
    unfold Params.obj2 Params.obj3
    nlinarith
  have hobj : M.obj3 w = M.α * q + (1 - M.α) * E := by
    unfold Params.obj3
    rw [mul_assoc, hAE]
  refine ⟨hce, h23, hβpos, hβ1, by linarith, by nlinarith, ?_⟩
  rw [hobj]
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 hA1)
          (show (0:ℝ) ≤ (1 - M.α) * M.vH by nlinarith)]

lemma ΔR_sq (M : Params) (hM : M.Standing) :
    M.ΔR ^ 2 = M.α * M.cL / ((1 - M.α) * (M.vH - M.vL)) := by
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  unfold Params.ΔR
  rw [Real.sq_sqrt]
  exact div_nonneg (mul_nonneg hα0.le hcL.le) (mul_nonneg (by linarith) (by linarith))

theorem t_relaxation (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    condExp w (thresh w M.cL) ≤ condExp w M.vL ∧ M.obj2 w ≤ M.obj3 w :=
  ⟨(core M hM w hw hF).1, (core M hM w hw hF).2.1⟩

theorem t_cdf_vL_lt (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    cdf w M.vL < (M.cH - M.cL) / (M.vH - M.vL) := by
  obtain ⟨-, -, hβ0, hβ1, hL, hH, -⟩ := core M hM w hw hF
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

theorem t_lemma_6_ii_a (M : Params) (hM : M.Standing) (h1 : M.ΔR < 1) (h2 : M.ΔR < M.bnd)
    (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ M.U1 := by
  obtain ⟨-, -, hβ0, hβ1, hL, hH, hX⟩ := core M hM w hw hF
  have hsq := ΔR_sq M hM
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  exact (key_bound _ _ _ _ _ _ _ _ _ hα0 hα1 hcL hv hβ0 hβ1 hL hH hX (Real.sqrt_nonneg _) hsq).1

theorem t_lemma_6_ii_b (M : Params) (hM : M.Standing) (h1 : M.ΔR < 1) (h2 : M.bnd ≤ M.ΔR)
    (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ M.U2 := by
  obtain ⟨-, -, hβ0, hβ1, hL, hH, hX⟩ := core M hM w hw hF
  have hsq := ΔR_sq M hM
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  exact (key_bound _ _ _ _ _ _ _ _ _ hα0 hα1 hcL hv hβ0 hβ1 hL hH hX (Real.sqrt_nonneg _) hsq).2 h2

theorem t_lemma_6_i (M : Params) (hM : M.Standing) (h1 : 1 ≤ M.ΔR) (w : ℝ →₀ ℝ)
    (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ max M.vL ((1 - M.α) * M.vH) := by
  obtain ⟨-, -, hβ0, hβ1, hL, hH, hX⟩ := core M hM w hw hF
  have hsq := ΔR_sq M hM
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  set β := cdf w M.vL
  set q := condExp w M.vL
  have hD : 0 < M.vH - M.vL := by linarith
  have hK : 0 < (1 - M.α) * (M.vH - M.vL) := mul_pos (by linarith) hD
  have hΔ' : M.α * M.cL = (1 - M.α) * (M.vH - M.vL) * M.ΔR ^ 2 := by
    have h1α : (1 - M.α) ≠ 0 := (by linarith : (0:ℝ) < 1 - M.α).ne'
    have := hD.ne'
    rw [hsq]; field_simp
  have hq : β * q < β * M.vL - M.cL := by nlinarith
  have hcoef : 0 < M.α + (1 - M.α) * β := by nlinarith
  have hXβ : β * M.obj3 w ≤ (M.α + (1 - M.α) * β) * (β * M.vL - M.cL) +
      (1 - M.α) * (1 - β) * M.vH * β := by
    have := mul_le_mul_of_nonneg_left hX hβ0.le
    nlinarith [mul_lt_mul_of_pos_left hq hcoef]
  -- β (vL - cL - X) ≥ (1-β)(α cL - (1-α) D β) ≥ 0
  have hsq1 : 1 ≤ M.ΔR ^ 2 := by nlinarith
  have hc1 : (1 - M.α) * (M.vH - M.vL) * β ≤ M.α * M.cL := by
    rw [hΔ']; nlinarith [mul_le_mul_of_nonneg_left hsq1 hK.le]
  have : β * M.obj3 w ≤ β * (M.vL - M.cL) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hc1)]
  have := le_of_mul_le_mul_left this hβ0
  exact le_trans this (le_trans (by linarith) (le_max_left _ _))

end RPProp3Sol

namespace RPProp3Sol

lemma gsum (w : ℝ →₀ ℝ) (c b y : ℝ) (f : ℝ → ℝ) :
    ∑ p ∈ (w.filter (· ≤ c) + Finsupp.single b y).support,
      (w.filter (· ≤ c) + Finsupp.single b y) p * f p =
      ∑ p ∈ w.support, (if p ≤ c then w p * f p else 0) + y * f b := by
  change Finsupp.sum _ (fun p m => m * f p) = _
  rw [Finsupp.sum_add_index' (by simp) (by intros; ring), Finsupp.sum_single_index (by simp)]
  congr 1
  unfold Finsupp.sum
  rw [Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · simp only [Finsupp.filter_apply, if_pos h]
  · rfl

lemma g_cdf (w : ℝ →₀ ℝ) (c b y x : ℝ) :
    cdf (w.filter (· ≤ c) + Finsupp.single b y) x =
      ∑ p ∈ w.support, (if p ≤ c then w p * (if p ≤ x then 1 else 0) else 0) +
        y * (if b ≤ x then 1 else 0) := by
  rw [cdf_eq, ← gsum w c b y (fun p => if p ≤ x then 1 else 0)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_ite, mul_one, mul_zero]

lemma g_pexp (w : ℝ →₀ ℝ) (c b y x : ℝ) :
    pexp (w.filter (· ≤ c) + Finsupp.single b y) x =
      ∑ p ∈ w.support, (if p ≤ c then w p * (if p ≤ x then p else 0) else 0) +
        y * (if b ≤ x then b else 0) := by
  rw [pexp_eq, ← gsum w c b y (fun p => if p ≤ x then p else 0)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_ite, mul_zero]

lemma g_gain (w : ℝ →₀ ℝ) (c b y v : ℝ) :
    gain (w.filter (· ≤ c) + Finsupp.single b y) v =
      ∑ p ∈ w.support, (if p ≤ c then w p * max (v - p) 0 else 0) + y * max (v - b) 0 := by
  unfold gain; rw [gsum]

lemma g_total (w : ℝ →₀ ℝ) (c b y : ℝ) :
    ((w.filter (· ≤ c) + Finsupp.single b y).sum fun _ m => m) = cdf w c + y := by
  have := gsum w c b y (fun _ => 1)
  simp only [mul_one] at this
  rw [cdf_eq]
  exact this

theorem t_lemma_5 (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    ∃ g : ℝ →₀ ℝ, IsPriceDist g ∧ M.Feas g ∧
      (∀ p, p ≤ M.vL → g p = w p) ∧
      (∀ p, M.vL < p → p ≠ M.vH → g p = 0) ∧
      g M.vH = 1 - cdf w M.vL ∧
      M.obj3 w ≤ M.obj3 g := by
  obtain ⟨-, -, hβ0, hβ1, -, -, -⟩ := core M hM w hw hF
  obtain ⟨hcL, hcLvL, hcH, hcHvH, hv, hα0, hα1⟩ := hM
  obtain ⟨hgL, hgH⟩ := hF
  have hcdfL : cdf (w.filter (· ≤ M.vL) + Finsupp.single M.vH (1 - cdf w M.vL)) M.vL =
      cdf w M.vL := by
    rw [g_cdf, if_neg (by linarith), mul_zero, add_zero, cdf_eq w M.vL]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ≤ M.vL <;> simp [h]
  have hcdfH : cdf (w.filter (· ≤ M.vL) + Finsupp.single M.vH (1 - cdf w M.vL)) M.vH = 1 := by
    rw [g_cdf, if_pos le_rfl, mul_one]
    have : ∑ p ∈ w.support, (if p ≤ M.vL then w p * (if p ≤ M.vH then 1 else 0) else 0) =
        cdf w M.vL := by
      rw [cdf_eq]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p ≤ M.vL
      · simp [h1, h1.trans hv.le]
      · simp [h1]
    rw [this]; ring
  have hpexpL : pexp (w.filter (· ≤ M.vL) + Finsupp.single M.vH (1 - cdf w M.vL)) M.vL =
      pexp w M.vL := by
    rw [g_pexp, if_neg (by linarith), mul_zero, add_zero, pexp_eq]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ≤ M.vL <;> simp [h]
  have hpexpH : pexp (w.filter (· ≤ M.vL) + Finsupp.single M.vH (1 - cdf w M.vL)) M.vH =
      pexp w M.vL + (1 - cdf w M.vL) * M.vH := by
    rw [g_pexp, if_pos le_rfl, pexp_eq]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h1 : p ≤ M.vL
    · simp [h1, h1.trans hv.le]
    · simp [h1]
  refine ⟨w.filter (· ≤ M.vL) + Finsupp.single M.vH (1 - cdf w M.vL),
    ⟨fun p => ?_, ?_⟩, ⟨?_, ?_⟩, fun p hp => ?_, fun p hp hne => ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.single_apply]
    have := hw.1 p
    split_ifs <;> linarith
  · rw [g_total]; ring
  · rw [g_gain, max_eq_right (by linarith : M.vL - M.vH ≤ 0), mul_zero, add_zero]
    convert hgL using 1
    unfold gain
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs with h
    · rfl
    · rw [max_eq_right (by linarith), mul_zero]
  · rw [g_gain, max_eq_right (by linarith : M.vH - M.vH ≤ 0), mul_zero, add_zero]
    refine le_trans ?_ hgH
    unfold gain
    refine Finset.sum_le_sum (fun p _ => ?_)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw.1 p) (le_max_right _ _)
  · rw [Finsupp.add_apply, Finsupp.filter_apply, if_pos hp,
      Finsupp.single_apply_eq_zero.2 (fun h => absurd hp (by rw [h]; exact not_le.2 hv)),
      add_zero]
  · rw [Finsupp.add_apply, Finsupp.filter_apply, if_neg (not_le.2 hp), zero_add,
      Finsupp.single_apply_eq_zero.2 (fun h => absurd h hne)]
  · rw [Finsupp.add_apply, Finsupp.filter_apply, if_neg (not_le.2 hv), Finsupp.single_eq_same,
      zero_add]
  · have hAβ := cdf_mono w hw hv.le
    have hA1 := cdf_le_one w hw M.vH
    have hdiff := pexp_diff w hw hv.le
    have hA0 : 0 < cdf w M.vH := lt_of_lt_of_le hβ0 hAβ
    unfold Params.obj3 condExp
    rw [hcdfL, hcdfH, hpexpL, hpexpH, div_one, mul_one]
    have : cdf w M.vH * (pexp w M.vH / cdf w M.vH) = pexp w M.vH := by field_simp
    rw [mul_assoc, this]
    nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 hA1)
          (show (0:ℝ) ≤ (1 - M.α) * M.vH by nlinarith)]

end RPProp3Sol

theorem solution (M : Params) (hM : M.Standing) (h1 : M.ΔR < 1) (h2 : M.bnd ≤ M.ΔR)
    (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ M.U2 :=
  RPProp3Sol.t_lemma_6_ii_b M hM h1 h2 w hw hF
