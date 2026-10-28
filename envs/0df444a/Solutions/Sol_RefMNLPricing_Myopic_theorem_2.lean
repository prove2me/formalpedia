-- Prove2me | solution 1 for RefMNLPricing.Myopic.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:45:13.670049+00:00
-- url     : https://prove2.me/submissions/ed9fb8ad-9210-4121-b640-3f7380cfc51f

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13

open RefMNLPricing.Myopic

namespace RefMNLT2Aux

/-- The one-dimensional profile `(x - v) e^{A - β x}`. -/
noncomputable def hh (β A v x : ℝ) : ℝ := (x - v) * Real.exp (A - β * x)

lemma hh_le (β A v x : ℝ) (hβ : 0 < β) :
    hh β A v x ≤ 1 / β * Real.exp (A - β * v - 1) := by
  unfold hh
  have h1 := Real.add_one_le_exp (β * (x - v) - 1)
  have e : Real.exp (A - β * v - 1) = Real.exp (β * (x - v) - 1) * Real.exp (A - β * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (A - β * x)
  have : (x - v) ≤ 1 / β * Real.exp (β * (x - v) - 1) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hβ]; nlinarith
  calc (x - v) * Real.exp (A - β * x)
      ≤ (1 / β * Real.exp (β * (x - v) - 1)) * Real.exp (A - β * x) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = _ := by ring

lemma hh_lt (β A v x : ℝ) (hβ : 0 < β) (hx : x ≠ v + 1 / β) :
    hh β A v x < 1 / β * Real.exp (A - β * v - 1) := by
  unfold hh
  have hne : β * (x - v) - 1 ≠ 0 := by
    intro h
    apply hx
    field_simp
    linarith
  have h1 := Real.add_one_lt_exp hne
  have e : Real.exp (A - β * v - 1) = Real.exp (β * (x - v) - 1) * Real.exp (A - β * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (A - β * x)
  have : (x - v) < 1 / β * Real.exp (β * (x - v) - 1) := by
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hβ]; nlinarith
  calc (x - v) * Real.exp (A - β * x)
      < (1 / β * Real.exp (β * (x - v) - 1)) * Real.exp (A - β * x) :=
        mul_lt_mul_of_pos_right this hpos
    _ = _ := by ring

lemma hh_peak (β A v : ℝ) (hβ : 0 < β) :
    hh β A v (v + 1 / β) = 1 / β * Real.exp (A - β * v - 1) := by
  unfold hh
  congr 2
  · ring
  · field_simp; ring

lemma hh_pos_peak (β A v : ℝ) (hβ : 0 < β) : 0 < 1 / β * Real.exp (A - β * v - 1) := by
  have := Real.exp_pos (A - β * v - 1)
  positivity

/-- Strictly increasing up to the peak. -/
lemma hh_inc (β A v x y : ℝ) (hβ : 0 < β) (hxy : x < y) (hy : y ≤ v + 1 / β) :
    hh β A v x < hh β A v y := by
  unfold hh
  have hE : Real.exp (A - β * x) = Real.exp (A - β * y) * Real.exp (β * (y - x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hE]
  have hEy := Real.exp_pos (A - β * y)
  have hβt2 : β * (y - v) ≤ 1 := by
    have : y - v ≤ 1 / β := by linarith
    calc β * (y - v) ≤ β * (1 / β) := mul_le_mul_of_nonneg_left this hβ.le
      _ = 1 := by field_simp
  suffices h : (x - v) * Real.exp (β * (y - x)) < (y - v) by
    calc (x - v) * (Real.exp (A - β * y) * Real.exp (β * (y - x)))
        = ((x - v) * Real.exp (β * (y - x))) * Real.exp (A - β * y) := by ring
      _ < (y - v) * Real.exp (A - β * y) := mul_lt_mul_of_pos_right h hEy
  have he1 : 1 ≤ Real.exp (β * (y - x)) := Real.one_le_exp (by nlinarith)
  rcases le_or_gt (y - v) 0 with h2 | h2
  · nlinarith
  · have hne : -(β * (y - x)) ≠ 0 := by nlinarith
    have h3 := Real.add_one_lt_exp hne
    have hprod : Real.exp (-(β * (y - x))) * Real.exp (β * (y - x)) = 1 := by
      rw [← Real.exp_add]; simp
    -- x - v < (y - v) * e'
    have h4 : x - v < (y - v) * Real.exp (-(β * (y - x))) := by nlinarith
    have h5 := mul_lt_mul_of_pos_right h4 (Real.exp_pos (β * (y - x)))
    calc (x - v) * Real.exp (β * (y - x))
        < (y - v) * Real.exp (-(β * (y - x))) * Real.exp (β * (y - x)) := h5
      _ = (y - v) * (Real.exp (-(β * (y - x))) * Real.exp (β * (y - x))) := by ring
      _ = y - v := by rw [hprod, mul_one]

/-- Strictly decreasing after the peak. -/
lemma hh_dec (β A v x y : ℝ) (hβ : 0 < β) (hx : v + 1 / β ≤ x) (hxy : x < y) :
    hh β A v y < hh β A v x := by
  unfold hh
  have hE : Real.exp (A - β * x) = Real.exp (A - β * y) * Real.exp (β * (y - x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hE]
  have hEy := Real.exp_pos (A - β * y)
  have hβt1 : 1 ≤ β * (x - v) := by
    have : 1 / β ≤ x - v := by linarith
    calc (1 : ℝ) = β * (1 / β) := by field_simp
      _ ≤ β * (x - v) := mul_le_mul_of_nonneg_left this hβ.le
  suffices h : (y - v) < (x - v) * Real.exp (β * (y - x)) by
    calc (y - v) * Real.exp (A - β * y)
        < ((x - v) * Real.exp (β * (y - x))) * Real.exp (A - β * y) :=
          mul_lt_mul_of_pos_right h hEy
      _ = (x - v) * (Real.exp (A - β * y) * Real.exp (β * (y - x))) := by ring
  have hne : β * (y - x) ≠ 0 := by nlinarith
  have h3 := Real.add_one_lt_exp hne
  have ht1 : 0 < x - v := by nlinarith
  nlinarith

/-- The per-product objective `(x - v) e^{u(x)}` with the kinked utility. -/
noncomputable def GG (a b cp cm r v x : ℝ) : ℝ :=
  (x - v) * Real.exp (a - b * x + cp * max (r - x) 0 - cm * max (x - r) 0)

lemma GG_left (a b cp cm r v x : ℝ) (hx : x ≤ r) :
    GG a b cp cm r v x = hh (b + cp) (a + cp * r) v x := by
  unfold GG hh
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  congr 2; ring

lemma GG_right (a b cp cm r v x : ℝ) (hx : r ≤ x) :
    GG a b cp cm r v x = hh (b + cm) (a + cm * r) v x := by
  unfold GG hh
  rw [max_eq_right (by linarith), max_eq_left (by linarith)]
  congr 2; ring

lemma GG_nonpos (a b cp cm r v x : ℝ) (hx : x ≤ v) : GG a b cp cm r v x ≤ 0 := by
  unfold GG
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

/-- For `c⁺ ≤ c⁻` the kinked utility is below both affine branches. -/
lemma GG_le_left (a b cp cm r v x : ℝ) (hc : cp ≤ cm) (hcp : 0 ≤ cp) (hx : v ≤ x) :
    GG a b cp cm r v x ≤ hh (b + cp) (a + cp * r) v x := by
  unfold GG hh
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.2
  rcases le_total x r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith

lemma GG_le_right (a b cp cm r v x : ℝ) (hc : cp ≤ cm) (hcp : 0 ≤ cp) (hx : v ≤ x) :
    GG a b cp cm r v x ≤ hh (b + cm) (a + cm * r) v x := by
  unfold GG hh
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.2
  rcases le_total x r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith

/-- For `c⁻ ≤ c⁺` the kinked utility is above both affine branches. -/
lemma GG_ge_left (a b cp cm r v x : ℝ) (hc : cm ≤ cp) (hcm : 0 ≤ cm) (hx : v ≤ x) :
    hh (b + cp) (a + cp * r) v x ≤ GG a b cp cm r v x := by
  unfold GG hh
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.2
  rcases le_total x r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith

lemma GG_ge_right (a b cp cm r v x : ℝ) (hc : cm ≤ cp) (hcm : 0 ≤ cm) (hx : v ≤ x) :
    hh (b + cm) (a + cm * r) v x ≤ GG a b cp cm r v x := by
  unfold GG hh
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.2
  rcases le_total x r with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith

/-- Non-strict bounds `1/y ≤ (log y - log x)/(y - x) ≤ 1/x` for `0 < x < y`. -/
lemma log_slope_bounds (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    1 / y ≤ (Real.log y - Real.log x) / (y - x) ∧
      (Real.log y - Real.log x) / (y - x) ≤ 1 / x := by
  have hy : 0 < y := lt_trans hx hxy
  have hyx : 0 < y - x := by linarith
  have hA : Real.log y - Real.log x ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at h
    have : y / x - 1 = (y - x) / x := by field_simp
    linarith
  have hB : (y - x) / y ≤ Real.log y - Real.log x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at h
    have : x / y - 1 = -((y - x) / y) := by field_simp; ring
    linarith
  constructor
  · rw [div_le_div_iff₀ hy hyx]
    have := (div_le_iff₀ hy).1 hB
    linarith
  · rw [div_le_div_iff₀ hyx hx]
    have := (le_div_iff₀ hx).1 hA
    linarith

/-- Comparing the two branch peaks of a gain-seeking product. -/
lemma peak_compare (a b cp cm r v : ℝ) (hb : 0 < b) (hcm : 0 ≤ cm) (hc : cm < cp) :
    (1 / (b + cp) * Real.exp ((a + cp * r) - (b + cp) * v - 1) <
        1 / (b + cm) * Real.exp ((a + cm * r) - (b + cm) * v - 1) ↔
      r < v + (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm)) := by
  have hx : 0 < b + cm := by linarith
  have hy : 0 < b + cp := by linarith
  have hd : 0 < cp - cm := by linarith
  have k : ∀ β K : ℝ, 0 < β → 1 / β * Real.exp K = Real.exp (K - Real.log β) := by
    intro β K hβ
    rw [Real.exp_sub, Real.exp_log hβ]; field_simp
  rw [k _ _ hy, k _ _ hx, Real.exp_lt_exp, ← sub_lt_iff_lt_add', lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

lemma peak_compare' (a b cp cm r v : ℝ) (hb : 0 < b) (hcm : 0 ≤ cm) (hc : cm < cp) :
    (1 / (b + cm) * Real.exp ((a + cm * r) - (b + cm) * v - 1) <
        1 / (b + cp) * Real.exp ((a + cp * r) - (b + cp) * v - 1) ↔
      v + (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) < r) := by
  have hx : 0 < b + cm := by linarith
  have hy : 0 < b + cp := by linarith
  have hd : 0 < cp - cm := by linarith
  have k : ∀ β K : ℝ, 0 < β → 1 / β * Real.exp K = Real.exp (K - Real.log β) := by
    intro β K hβ
    rw [Real.exp_sub, Real.exp_log hβ]; field_simp
  rw [k _ _ hy, k _ _ hx, Real.exp_lt_exp, ← lt_sub_iff_add_lt', div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- Uniqueness principle: a box maximiser of a function with a strict maximiser in the box. -/
lemma eq_of_strict (G : ℝ → ℝ) (pH y xs : ℝ)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) pH, G x ≤ G y) (hxs : xs ∈ Set.Icc (0 : ℝ) pH)
    (hstrict : ∀ z, z ≠ xs → G z < G xs) : y = xs := by
  by_contra h
  have h1 := hmax xs hxs
  have h2 := hstrict y h
  linarith

/-- One-dimensional form of Theorem 2. -/
lemma oneD (a b cp cm r v pH y : ℝ) (hb : 0 < b) (hcp : 0 ≤ cp) (hcm : 0 ≤ cm)
    (hv : 0 ≤ v) (hvχ : v + 1 / (b + min cp cm) ≤ pH) (hr : r ∈ Set.Icc (0 : ℝ) pH)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) pH, GG a b cp cm r v x ≤ GG a b cp cm r v y) :
    (cp < cm →
        (r < v + 1 / (b + cm) → y = v + 1 / (b + cm)) ∧
        (v + 1 / (b + cp) < r → y = v + 1 / (b + cp)) ∧
        (v + 1 / (b + cm) ≤ r → r ≤ v + 1 / (b + cp) → y = r)) ∧
      (cp = cm → y = v + 1 / (b + cp)) ∧
      (cm < cp →
        (1 / (b + cp) ≤ (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) ∧
          (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) ≤ 1 / (b + cm)) ∧
        (r < v + (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) → y = v + 1 / (b + cm)) ∧
        (v + (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) < r → y = v + 1 / (b + cp)) ∧
        (r = v + (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) →
          y = v + 1 / (b + cm) ∨ y = v + 1 / (b + cp))) := by
  have hβp : 0 < b + cp := by linarith
  have hβm : 0 < b + cm := by linarith
  have hip : 0 < 1 / (b + cp) := by positivity
  have him : 0 < 1 / (b + cm) := by positivity
  -- candidates lie in the box
  have hboxp : v + 1 / (b + cp) ∈ Set.Icc (0 : ℝ) pH := by
    refine ⟨by linarith, ?_⟩
    have : 1 / (b + cp) ≤ 1 / (b + min cp cm) :=
      one_div_le_one_div_of_le (by rcases min_choice cp cm with h | h <;> rw [h] <;> linarith)
        (by linarith [min_le_left cp cm])
    linarith
  have hboxm : v + 1 / (b + cm) ∈ Set.Icc (0 : ℝ) pH := by
    refine ⟨by linarith, ?_⟩
    have : 1 / (b + cm) ≤ 1 / (b + min cp cm) :=
      one_div_le_one_div_of_le (by rcases min_choice cp cm with h | h <;> rw [h] <;> linarith)
        (by linarith [min_le_right cp cm])
    linarith
  set G := GG a b cp cm r v with hG
  set ML := 1 / (b + cp) * Real.exp ((a + cp * r) - (b + cp) * v - 1) with hML
  set MR := 1 / (b + cm) * Real.exp ((a + cm * r) - (b + cm) * v - 1) with hMR
  have hMLpos : 0 < ML := hh_pos_peak _ _ _ hβp
  have hMRpos : 0 < MR := hh_pos_peak _ _ _ hβm
  -- loss-averse / neutral : the two "branch-peak" cases
  have caseR : cp ≤ cm → r ≤ v + 1 / (b + cm) → y = v + 1 / (b + cm) := by
    intro hc hrl
    refine eq_of_strict G pH y _ hmax hboxm (fun z hz => ?_)
    have hpk : G (v + 1 / (b + cm)) = MR := by
      rw [hG, GG_right _ _ _ _ _ _ _ hrl, hh_peak _ _ _ hβm]
    rw [hpk]
    rcases le_or_gt z v with hzv | hzv
    · have := GG_nonpos a b cp cm r v z hzv; linarith
    · calc G z ≤ hh (b + cm) (a + cm * r) v z := GG_le_right _ _ _ _ _ _ _ hc hcp hzv.le
        _ < MR := hh_lt _ _ _ _ hβm hz
  have caseL : cp ≤ cm → v + 1 / (b + cp) ≤ r → y = v + 1 / (b + cp) := by
    intro hc hrl
    refine eq_of_strict G pH y _ hmax hboxp (fun z hz => ?_)
    have hpk : G (v + 1 / (b + cp)) = ML := by
      rw [hG, GG_left _ _ _ _ _ _ _ hrl, hh_peak _ _ _ hβp]
    rw [hpk]
    rcases le_or_gt z v with hzv | hzv
    · have := GG_nonpos a b cp cm r v z hzv; linarith
    · calc G z ≤ hh (b + cp) (a + cp * r) v z := GG_le_left _ _ _ _ _ _ _ hc hcp hzv.le
        _ < ML := hh_lt _ _ _ _ hβp hz
  -- gain-seeking: Z bounds
  have hZb : cm < cp → 1 / (b + cp) ≤ (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) ∧
      (Real.log (b + cp) - Real.log (b + cm)) / (cp - cm) ≤ 1 / (b + cm) := by
    intro hc
    have := log_slope_bounds (b + cm) (b + cp) hβm (by linarith)
    have e : (b + cp) - (b + cm) = cp - cm := by ring
    rw [e] at this
    exact this
  -- gain-seeking: upper bound on G off the peaks
  have gsU : cm < cp → ∀ z, v < z → (G z ≤ hh (b + cp) (a + cp * r) v z ∨
      G z ≤ hh (b + cm) (a + cm * r) v z) := by
    intro hc z hz
    rcases le_total z r with h | h
    · left; rw [hG, GG_left _ _ _ _ _ _ _ h]
    · right; rw [hG, GG_right _ _ _ _ _ _ _ h]
  refine ⟨fun hc => ⟨fun h => caseR hc.le h.le, fun h => caseL hc.le h.le, fun h1 h2 => ?_⟩,
    fun hc => ?_, fun hc => ⟨hZb hc, fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · -- middle region: the maximiser is `r`
    refine eq_of_strict G pH y r hmax hr (fun z hz => ?_)
    rcases lt_or_gt_of_ne hz with hzr | hzr
    · rw [hG, GG_left _ _ _ _ _ _ _ hzr.le, GG_left _ _ _ _ _ _ _ le_rfl]
      exact hh_inc _ _ _ _ _ hβp hzr h2
    · rw [hG, GG_right _ _ _ _ _ _ _ hzr.le, GG_right _ _ _ _ _ _ _ le_rfl]
      exact hh_dec _ _ _ _ _ hβm h1 hzr
  · -- loss-neutral
    refine eq_of_strict G pH y _ hmax hboxp (fun z hz => ?_)
    have hpk : G (v + 1 / (b + cp)) = ML := by
      rcases le_total (v + 1 / (b + cp)) r with h | h
      · rw [hG, GG_left _ _ _ _ _ _ _ h, hh_peak _ _ _ hβp]
      · rw [hG, GG_right _ _ _ _ _ _ _ h, ← hc, hh_peak _ _ _ hβp]
    rw [hpk]
    rcases le_or_gt z v with hzv | hzv
    · have := GG_nonpos a b cp cm r v z hzv; linarith
    · calc G z ≤ hh (b + cp) (a + cp * r) v z := GG_le_left _ _ _ _ _ _ _ hc.le hcp hzv.le
        _ < ML := hh_lt _ _ _ _ hβp hz
  · -- gain-seeking, below threshold
    have hlt : ML < MR := (peak_compare a b cp cm r v hb hcm hc).2 h
    refine eq_of_strict G pH y _ hmax hboxm (fun z hz => ?_)
    have hpk : MR ≤ G (v + 1 / (b + cm)) := by
      rw [hMR, ← hh_peak _ _ _ hβm]
      exact GG_ge_right _ _ _ _ _ _ _ hc.le hcm (by linarith)
    rcases le_or_gt z v with hzv | hzv
    · have := GG_nonpos a b cp cm r v z hzv; linarith
    · rcases gsU hc z hzv with h1 | h1
      · have := hh_le (b + cp) (a + cp * r) v z hβp; linarith
      · have := hh_lt (b + cm) (a + cm * r) v z hβm hz; linarith
  · -- gain-seeking, above threshold
    have hlt : MR < ML := (peak_compare' a b cp cm r v hb hcm hc).2 h
    refine eq_of_strict G pH y _ hmax hboxp (fun z hz => ?_)
    have hpk : ML ≤ G (v + 1 / (b + cp)) := by
      rw [hML, ← hh_peak _ _ _ hβp]
      exact GG_ge_left _ _ _ _ _ _ _ hc.le hcm (by linarith)
    rcases le_or_gt z v with hzv | hzv
    · have := GG_nonpos a b cp cm r v z hzv; linarith
    · rcases gsU hc z hzv with h1 | h1
      · have := hh_lt (b + cp) (a + cp * r) v z hβp hz; linarith
      · have := hh_le (b + cm) (a + cm * r) v z hβm; linarith
  · -- gain-seeking, at the threshold
    have hn1 : ¬ ML < MR := fun h' => absurd ((peak_compare a b cp cm r v hb hcm hc).1 h') (by
      rw [h]; exact lt_irrefl _)
    have hn2 : ¬ MR < ML := fun h' => absurd ((peak_compare' a b cp cm r v hb hcm hc).1 h') (by
      rw [h]; exact lt_irrefl _)
    have heq : ML = MR := by push_neg at hn1 hn2; linarith
    by_contra hne
    push_neg at hne
    obtain ⟨hne1, hne2⟩ := hne
    have hpk : ML ≤ G (v + 1 / (b + cp)) := by
      rw [hML, ← hh_peak _ _ _ hβp]
      exact GG_ge_left _ _ _ _ _ _ _ hc.le hcm (by linarith)
    have hy := hmax _ hboxp
    rcases le_or_gt y v with hzv | hzv
    · have := GG_nonpos a b cp cm r v y hzv; linarith
    · rcases gsU hc y hzv with h1 | h1
      · have := hh_lt (b + cp) (a + cp * r) v y hβp hne2; linarith
      · have := hh_lt (b + cm) (a + cm * r) v y hβm hne1; linarith

/-- Pointwise bound used for the ceiling: if `r - v ≤ χ` then the per-product objective is at most
`1/(b+c⁺) · exp(a - b v + c⁺ χ - 1)`. -/
lemma gbound (a b cp cm r v χ x : ℝ) (hb : 0 < b) (hcp : 0 ≤ cp) (hcm : 0 ≤ cm)
    (hχ : 1 / (b + min cp cm) ≤ χ) (hrv : r - v ≤ χ) :
    GG a b cp cm r v x ≤ 1 / (b + cp) * Real.exp (a - b * v + cp * χ - 1) := by
  have hβp : 0 < b + cp := by linarith
  have hβm : 0 < b + cm := by linarith
  have hRpos : 0 < 1 / (b + cp) * Real.exp (a - b * v + cp * χ - 1) := by positivity
  rcases le_or_gt x v with hxv | hxv
  · have := GG_nonpos a b cp cm r v x hxv; linarith
  by_cases hA : cp ≤ cm ∨ x - v ≤ χ
  · have hE : a - b * x + cp * max (r - x) 0 - cm * max (x - r) 0 ≤
        (a + cp * χ + cp * v) - (b + cp) * x := by
      rcases le_total x r with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        have : cp * (r - x) ≤ cp * (χ + v - x) := mul_le_mul_of_nonneg_left (by linarith) hcp
        nlinarith
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        rcases hA with hA | hA
        · nlinarith
        · nlinarith
    calc GG a b cp cm r v x ≤ hh (b + cp) (a + cp * χ + cp * v) v x := by
          unfold GG hh
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE) (by linarith)
      _ ≤ 1 / (b + cp) * Real.exp ((a + cp * χ + cp * v) - (b + cp) * v - 1) := hh_le _ _ _ _ hβp
      _ = 1 / (b + cp) * Real.exp (a - b * v + cp * χ - 1) := by ring_nf
  · push_neg at hA
    obtain ⟨hc, hxχ⟩ := hA
    have hmin : min cp cm = cm := min_eq_right hc.le
    rw [hmin] at hχ
    have hχ' : 1 ≤ (b + cm) * χ := by
      rw [div_le_iff₀ hβm] at hχ; linarith
    have hxr : r ≤ x := by linarith
    have hE : a - b * x + cp * max (r - x) 0 - cm * max (x - r) 0 ≤
        (a + cm * χ + cm * v) - (b + cm) * x := by
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      nlinarith
    have step1 : GG a b cp cm r v x ≤ 1 / (b + cm) * Real.exp (a - b * v + cm * χ - 1) :=
      calc GG a b cp cm r v x ≤ hh (b + cm) (a + cm * χ + cm * v) v x := by
            unfold GG hh
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE) (by linarith)
        _ ≤ 1 / (b + cm) * Real.exp ((a + cm * χ + cm * v) - (b + cm) * v - 1) :=
            hh_le _ _ _ _ hβm
        _ = 1 / (b + cm) * Real.exp (a - b * v + cm * χ - 1) := by ring_nf
    refine step1.trans ?_
    have hsplit : Real.exp (a - b * v + cp * χ - 1) =
        Real.exp (a - b * v + cm * χ - 1) * Real.exp ((cp - cm) * χ) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have hY := Real.add_one_le_exp ((cp - cm) * χ)
    have hX := Real.exp_pos (a - b * v + cm * χ - 1)
    have hkey : 1 / (b + cm) ≤ 1 / (b + cp) * Real.exp ((cp - cm) * χ) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hβm hβp, one_mul]
      have : (cp - cm) ≤ (cp - cm) * ((b + cm) * χ) := by
        have := mul_le_mul_of_nonneg_left hχ' (by linarith : (0:ℝ) ≤ cp - cm)
        linarith
      nlinarith
    calc 1 / (b + cm) * Real.exp (a - b * v + cm * χ - 1)
        ≤ (1 / (b + cp) * Real.exp ((cp - cm) * χ)) * Real.exp (a - b * v + cm * χ - 1) :=
          mul_le_mul_of_nonneg_right hkey hX.le
      _ = _ := by ring

end RefMNLT2Aux

namespace RefMNLT2Aux
variable {n : ℕ}

lemma rev_mul (a b cp cm q r : Fin n → ℝ) :
    revenue a b cp cm q r * (1 + ∑ k, Real.exp (util a b cp cm q r k)) =
      ∑ k, q k * Real.exp (util a b cp cm q r k) := by
  have hD : 0 < 1 + ∑ k, Real.exp (util a b cp cm q r k) := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
      (Real.exp_pos (util a b cp cm q r k)).le)
    linarith
  unfold revenue share
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp

lemma GG_util (a b cp cm q r : Fin n → ℝ) (v : ℝ) (k : Fin n) :
    GG (a k) (b k) (cp k) (cm k) (r k) v (q k) = (q k - v) * Real.exp (util a b cp cm q r k) := rfl

lemma sum_GG (a b cp cm q r : Fin n → ℝ) (v : ℝ) :
    ∑ k, GG (a k) (b k) (cp k) (cm k) (r k) v (q k) =
      revenue a b cp cm q r * (1 + ∑ k, Real.exp (util a b cp cm q r k)) -
        v * ∑ k, Real.exp (util a b cp cm q r k) := by
  rw [rev_mul]
  simp_rw [GG_util, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

lemma sum_GG_le (a b cp cm q r : Fin n → ℝ) (v : ℝ) (h : revenue a b cp cm q r ≤ v) :
    ∑ k, GG (a k) (b k) (cp k) (cm k) (r k) v (q k) ≤ v := by
  rw [sum_GG]
  have hS : 0 ≤ ∑ k, Real.exp (util a b cp cm q r k) :=
    Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  nlinarith

lemma sum_GG_eq (a b cp cm q r : Fin n → ℝ) :
    ∑ k, GG (a k) (b k) (cp k) (cm k) (r k) (revenue a b cp cm q r) (q k) =
      revenue a b cp cm q r := by
  rw [sum_GG]; ring

lemma coord_max (a b cp cm : Fin n → ℝ) (pH : ℝ) (r p : Fin n → ℝ)
    (hp : IsBoxMax a b cp cm pH r p) (i : Fin n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) pH) :
    GG (a i) (b i) (cp i) (cm i) (r i) (revenue a b cp cm p r) x ≤
      GG (a i) (b i) (cp i) (cm i) (r i) (revenue a b cp cm p r) (p i) := by
  set v := revenue a b cp cm p r
  set q := Function.update p i x with hq
  have hqbox : InBox pH q := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [hq, hx]
    · rw [hq, Function.update_of_ne hk]; exact hp.1 k
  have h1 := sum_GG_le a b cp cm q r v (hp.2 q hqbox)
  have h2 := sum_GG_eq a b cp cm p r
  have e1 := (Finset.add_sum_erase Finset.univ
    (fun k => GG (a k) (b k) (cp k) (cm k) (r k) v (q k)) (Finset.mem_univ i)).symm
  have e2 := (Finset.add_sum_erase Finset.univ
    (fun k => GG (a k) (b k) (cp k) (cm k) (r k) v (p k)) (Finset.mem_univ i)).symm
  have e3 : ∑ k ∈ Finset.univ.erase i, GG (a k) (b k) (cp k) (cm k) (r k) v (q k) =
      ∑ k ∈ Finset.univ.erase i, GG (a k) (b k) (cp k) (cm k) (r k) v (p k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hq, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hqi : q i = x := by simp [hq]
  rw [hqi] at e1
  linarith

lemma rev_nonneg (a b cp cm : Fin n → ℝ) (pH : ℝ) (r p : Fin n → ℝ) (hp : InBox pH p) :
    0 ≤ revenue a b cp cm p r := by
  unfold revenue share
  refine Finset.sum_nonneg (fun k _ => mul_nonneg (hp k).1 (div_nonneg (Real.exp_pos _).le ?_))
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
    (Real.exp_pos (util a b cp cm p r k)).le)
  linarith

lemma chi_ge (a b cp cm : Fin n → ℝ) (i : Fin n) :
    1 / (b i + min (cp i) (cm i)) ≤ chi a b cp cm := by
  unfold chi
  exact le_ciSup (f := fun i => 1 / (b i + min (cp i) (cm i))) (Set.finite_range _).bddAbove i

lemma ceil_bound (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hceil : CeilingOK a b cp cm pH) (r p : Fin n → ℝ) (hr : InBox pH r)
    (hp : IsBoxMax a b cp cm pH r p) :
    revenue a b cp cm p r + chi a b cp cm ≤ pH := by
  set v := revenue a b cp cm p r
  set χ := chi a b cp cm
  by_contra hlt
  push_neg at hlt
  have hrk : ∀ k, r k - v ≤ χ := fun k => by linarith [(hr k).2]
  have hsum : v ≤ ∑ k, 1 / (b k + cp k) * Real.exp (a k - b k * v + cp k * χ - 1) := by
    calc v = ∑ k, GG (a k) (b k) (cp k) (cm k) (r k) v (p k) := (sum_GG_eq a b cp cm p r).symm
      _ ≤ _ := Finset.sum_le_sum (fun k _ =>
          gbound _ _ _ _ _ _ _ _ (hb k) (hcp k) (hcm k) (chi_ge a b cp cm k) (hrk k))
  obtain ⟨pHat, hfix, hle⟩ := hceil
  have hval : ∑ k, 1 / (b k + cp k) * Real.exp (a k - b k * (pHat - χ) + cp k * χ - 1) =
      pHat - χ := by
    have : ceilRHS a b cp cm pHat = χ +
        ∑ k, 1 / (b k + cp k) * Real.exp (a k - b k * (pHat - χ) + cp k * χ - 1) := by
      unfold ceilRHS
      refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_))
      congr 2; ring
    linarith
  by_cases h2 : v ≤ pHat - χ
  · linarith
  · push_neg at h2
    have : ∑ k, 1 / (b k + cp k) * Real.exp (a k - b k * v + cp k * χ - 1) ≤
        ∑ k, 1 / (b k + cp k) * Real.exp (a k - b k * (pHat - χ) + cp k * χ - 1) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hβ : 0 < 1 / (b k + cp k) := by have := hb k; have := hcp k; positivity
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hβ.le
      have := hb k
      nlinarith
    linarith

end RefMNLT2Aux

open RefMNLT2Aux in
theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r p : Fin n → ℝ) (hr : InBox pH r) (hp : IsBoxMax a b cp cm pH r p) :
    ∀ i : Fin n,
      (cp i < cm i →
        (r i < revenue a b cp cm p r + 1 / (b i + cm i) →
          p i = revenue a b cp cm p r + 1 / (b i + cm i)) ∧
        (revenue a b cp cm p r + 1 / (b i + cp i) < r i →
          p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
        (revenue a b cp cm p r + 1 / (b i + cm i) ≤ r i →
          r i ≤ revenue a b cp cm p r + 1 / (b i + cp i) → p i = r i)) ∧
      (cp i = cm i → p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
      (cm i < cp i →
        (1 / (b i + cp i) ≤ Zgap b cp cm i ∧ Zgap b cp cm i ≤ 1 / (b i + cm i)) ∧
        (r i < revenue a b cp cm p r + Zgap b cp cm i →
          p i = revenue a b cp cm p r + 1 / (b i + cm i)) ∧
        (revenue a b cp cm p r + Zgap b cp cm i < r i →
          p i = revenue a b cp cm p r + 1 / (b i + cp i)) ∧
        (r i = revenue a b cp cm p r + Zgap b cp cm i →
          p i = revenue a b cp cm p r + 1 / (b i + cm i) ∨
            p i = revenue a b cp cm p r + 1 / (b i + cp i))) := by
  intro i
  have hcb := ceil_bound a b cp cm pH hb hcp hcm hceil r p hr hp
  have hχ := chi_ge a b cp cm i
  exact oneD (a i) (b i) (cp i) (cm i) (r i) (revenue a b cp cm p r) pH (p i) (hb i) (hcp i)
    (hcm i) (rev_nonneg a b cp cm pH r p hp.1) (by linarith) (hr i)
    (coord_max a b cp cm pH r p hp i)
