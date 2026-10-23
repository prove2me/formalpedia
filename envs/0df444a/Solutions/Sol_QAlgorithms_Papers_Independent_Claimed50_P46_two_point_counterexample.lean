-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P46.two_point_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:27:20.6443+00:00
-- url     : https://prove2.me/submissions/f9c4af84-6b83-4872-bd01-b667b55fa0ce

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section
open Filter
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P46

def X7_E (k : ℕ) (β : ℝ) : ℝ := Real.exp (-((k : ℝ) + 1) * β)

lemma X7_E_pos (k : ℕ) (β : ℝ) : 0 < X7_E k β := Real.exp_pos _

lemma X7_E_le_one (k : ℕ) {β : ℝ} (hβ : 0 ≤ β) : X7_E k β ≤ 1 := by
  unfold X7_E
  rw [Real.exp_le_one_iff]
  have : (0:ℝ) ≤ (k:ℝ) + 1 := by positivity
  nlinarith

lemma X7_bee_exp (k : ℕ) (t : ℝ) :
    blockErrorExponent k (ENNReal.ofReal (X7_E k t)) = (t : EReal) := by
  unfold blockErrorExponent perBlock X7_E
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_mul, ← EReal.coe_neg]
  congr 1
  have : (k:ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma X7_bee_anti (k : ℕ) {x y : ℝ≥0∞} (h : x ≤ y) :
    blockErrorExponent k y ≤ blockErrorExponent k x := by
  unfold blockErrorExponent perBlock
  rw [EReal.neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log h) (EReal.coe_nonneg.mpr (by positivity))

lemma X7_bee_ge (k : ℕ) {x : ℝ≥0∞} {t : ℝ} (h : x ≤ ENNReal.ofReal (X7_E k t)) :
    (t : EReal) ≤ blockErrorExponent k x := by
  rw [← X7_bee_exp k t]; exact X7_bee_anti k h

lemma X7_bee_le (k : ℕ) {x : ℝ≥0∞} {t : ℝ} (h : ENNReal.ofReal (X7_E k t) ≤ x) :
    blockErrorExponent k x ≤ (t : EReal) := by
  rw [← X7_bee_exp k t]; exact X7_bee_anti k h

lemma X7_bee_one (k : ℕ) : blockErrorExponent k 1 = 0 := by
  simp [blockErrorExponent, perBlock]

lemma X7_bee_nonneg (k : ℕ) {x : ℝ≥0∞} (h : x ≤ 1) : 0 ≤ blockErrorExponent k x := by
  rw [← X7_bee_one k]; exact X7_bee_anti k h

lemma X7_sum (k : ℕ) {β : ℝ} (hβ : 0 ≤ β) (f : Bool → Set.Icc (0:ℝ) 1) :
    (∑' x : Bool, ((Real.toNNReal (if x then 1 - Real.exp (-((k : ℝ) + 1) * β)
      else Real.exp (-((k : ℝ) + 1) * β)) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (f x).val)
    = ENNReal.ofReal (X7_E k β * (f false).val + (1 - X7_E k β) * (f true).val) := by
  have h1 := X7_E_le_one k hβ
  have h0 := X7_E_pos k β
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have e1 : ((Real.toNNReal (1 - Real.exp (-((k : ℝ) + 1) * β)) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (1 - X7_E k β) := rfl
  have e2 : ((Real.toNNReal (Real.exp (-((k : ℝ) + 1) * β)) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (X7_E k β) := rfl
  rw [e1, e2, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul h0.le,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (f true).2.1) (mul_nonneg h0.le (f false).2.1)]
  congr 1; ring


lemma X7_rev_rho (C : ClassicalData) (x : C.X) : (reverseClassical C).rho x = C.sigma x := rfl
lemma X7_rev_sigma (C : ClassicalData) (x : C.X) : (reverseClassical C).sigma x = C.rho x := rfl

section TP
variable (b : ℕ → ℝ) (c : ℝ)

lemma X7_rho_false (k : ℕ) : (((twoPointData b c k).rho false : ℝ≥0) : ℝ) = X7_E k (b k) := by
  simp [twoPointData, X7_E, (Real.exp_pos _).le]

lemma X7_sigma_false (k : ℕ) : (((twoPointData b c k).sigma false : ℝ≥0) : ℝ) = X7_E k c := by
  simp [twoPointData, X7_E, (Real.exp_pos _).le]

lemma X7_rho_true (k : ℕ) (hb : 0 ≤ b k) :
    (((twoPointData b c k).rho true : ℝ≥0) : ℝ) = 1 - X7_E k (b k) := by
  have := X7_E_le_one k hb
  simp only [twoPointData, if_true]
  rw [Real.coe_toNNReal _ (by unfold X7_E at this; linarith)]; rfl

lemma X7_sigma_true (k : ℕ) (hc : 0 ≤ c) :
    (((twoPointData b c k).sigma true : ℝ≥0) : ℝ) = 1 - X7_E k c := by
  have := X7_E_le_one k hc
  simp only [twoPointData, if_true]
  rw [Real.coe_toNNReal _ (by unfold X7_E at this; linarith)]; rfl

lemma X7_typeI (k : ℕ) (hb : 0 ≤ b k)
    (T : SimpleHypothesisTest (.classical (twoPointData b c k))) :
    testingTypeI T = ENNReal.ofReal (X7_E k (b k) * (1 - (T false).val)
      + (1 - X7_E k (b k)) * (1 - (T true).val)) :=
  X7_sum k hb (fun x => (testRejection (P := .classical (twoPointData b c k)) T) x)

lemma X7_typeIIc (k : ℕ) (hc : 0 ≤ c)
    (T : SimpleHypothesisTest (.classical (twoPointData b c k))) :
    testingTypeII (testRejection T) = ENNReal.ofReal (X7_E k c * (1 - (T false).val)
      + (1 - X7_E k c) * (1 - (T true).val)) :=
  X7_sum k hc (fun x => (testRejection (P := .classical (twoPointData b c k)) T) x)

lemma X7_revTypeI (k : ℕ) (hc : 0 ≤ c)
    (T : SimpleHypothesisTest (.classical (reverseClassical (twoPointData b c k)))) :
    testingTypeI T = ENNReal.ofReal (X7_E k c * (1 - (T false).val)
      + (1 - X7_E k c) * (1 - (T true).val)) :=
  X7_sum k hc (fun x => (testRejection (P := .classical (reverseClassical (twoPointData b c k))) T) x)


lemma X7_sv_false (k : ℕ) (a : ℝ) :
    (strictClassicalTest (twoPointData b c k) k a false).val =
      if X7_E k (b k) > Real.exp (((k:ℝ) + 1) * a) * X7_E k c then 1 else 0 := by
  unfold strictClassicalTest
  rw [X7_rho_false, X7_sigma_false]
  split_ifs <;> rfl

lemma X7_sv_true (k : ℕ) (a : ℝ) (hb : 0 ≤ b k) (hc : 0 ≤ c) :
    (strictClassicalTest (twoPointData b c k) k a true).val =
      if 1 - X7_E k (b k) > Real.exp (((k:ℝ) + 1) * a) * (1 - X7_E k c) then 1 else 0 := by
  unfold strictClassicalTest
  rw [X7_rho_true b c k hb, X7_sigma_true b c k hc]
  split_ifs <;> rfl

lemma X7_rv_false (k : ℕ) (a : ℝ) :
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a false).val =
      if X7_E k c > Real.exp (((k:ℝ) + 1) * a) * X7_E k (b k) then 1 else 0 := by
  unfold strictClassicalTest
  erw [X7_sigma_false b c k, X7_rho_false b c k]
  split_ifs <;> rfl

lemma X7_rv_true (k : ℕ) (a : ℝ) (hb : 0 ≤ b k) (hc : 0 ≤ c) :
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a true).val =
      if 1 - X7_E k c > Real.exp (((k:ℝ) + 1) * a) * (1 - X7_E k (b k)) then 1 else 0 := by
  unfold strictClassicalTest
  erw [X7_sigma_true b c k hc, X7_rho_true b c k hb]
  split_ifs <;> rfl

end TP

lemma X7_exp_mul_E (k : ℕ) (a β : ℝ) :
    Real.exp (((k:ℝ) + 1) * a) * X7_E k β = X7_E k (β - a) := by
  unfold X7_E; rw [← Real.exp_add]; congr 1; ring

lemma X7_E_lt (k : ℕ) {β γ : ℝ} (h : β < γ) : X7_E k γ < X7_E k β := by
  unfold X7_E; rw [Real.exp_lt_exp]
  have : (0:ℝ) < (k:ℝ) + 1 := by positivity
  nlinarith

lemma X7_E_le (k : ℕ) {β γ : ℝ} (h : β ≤ γ) : X7_E k γ ≤ X7_E k β := by
  unfold X7_E; rw [Real.exp_le_exp]
  have : (0:ℝ) < (k:ℝ) + 1 := by positivity
  nlinarith

lemma X7_ev_nat (N : ℝ) : ∀ᶠ k : ℕ in atTop, N ≤ (k:ℝ) + 1 := by
  filter_upwards [eventually_ge_atTop ⌈N⌉₊] with k hk
  have h1 := Nat.le_ceil N
  have h2 : (⌈N⌉₊:ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma X7_E_le_half (k : ℕ) {β : ℝ} (h : 1 ≤ ((k:ℝ) + 1) * β) : X7_E k β ≤ 1 / 2 := by
  unfold X7_E
  have h1 := Real.add_one_le_exp (((k:ℝ) + 1) * β)
  have h2 : Real.exp (-((k:ℝ) + 1) * β) * Real.exp (((k:ℝ) + 1) * β) = 1 := by
    rw [← Real.exp_add]; rw [show -((k:ℝ) + 1) * β + ((k:ℝ) + 1) * β = 0 by ring]; simp
  have h3 := Real.exp_pos (-((k:ℝ) + 1) * β)
  nlinarith

lemma X7_exp_ge_two (k : ℕ) {a : ℝ} (h : 1 ≤ ((k:ℝ) + 1) * a) : 2 ≤ Real.exp (((k:ℝ) + 1) * a) := by
  have h1 := Real.add_one_le_exp (((k:ℝ) + 1) * a); linarith


end QAlgorithms.Papers.Independent.Claimed50.P46



namespace QAlgorithms.Papers.Independent.Claimed50.P46

section EV
variable {b : ℕ → ℝ} {c : ℝ} (hb : ∀ k, 0 < b k) (hbinfty : Tendsto b atTop atTop) (hc : 0 < c)
include hb hbinfty hc

lemma X7_ev1 {a : ℝ} (ha : a ≤ 0) : ∀ᶠ k in atTop,
    (strictClassicalTest (twoPointData b c k) k a false).val = 0 ∧
    (strictClassicalTest (twoPointData b c k) k a true).val = 1 := by
  filter_upwards [hbinfty.eventually_gt_atTop (c - a)] with k hk
  rw [X7_sv_false, X7_sv_true b c k a (hb k).le hc.le, X7_exp_mul_E]
  have hn : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have e1 : Real.exp (((k:ℝ) + 1) * a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 := X7_E_le_one k hc.le
  have e3 : X7_E k (b k) < X7_E k c := X7_E_lt k (by linarith)
  constructor
  · rw [if_neg (not_lt.mpr (X7_E_le k hk.le))]
  · rw [if_pos (by nlinarith)]

lemma X7_ev2 {a : ℝ} (ha : 0 < a) : ∀ᶠ k in atTop,
    (strictClassicalTest (twoPointData b c k) k a false).val = 0 ∧
    (strictClassicalTest (twoPointData b c k) k a true).val = 0 := by
  filter_upwards [hbinfty.eventually_gt_atTop (c - a), X7_ev_nat (1/a), X7_ev_nat (1/c)] with k hk h1 h2
  rw [X7_sv_false, X7_sv_true b c k a (hb k).le hc.le, X7_exp_mul_E]
  have h1' : 1 ≤ ((k:ℝ) + 1) * a := by rw [div_le_iff₀ ha] at h1; linarith
  have h2' : 1 ≤ ((k:ℝ) + 1) * c := by rw [div_le_iff₀ hc] at h2; linarith
  have e1 := X7_exp_ge_two k h1'
  have e2 := X7_E_le_half k h2'
  have e3 := X7_E_pos k (b k)
  constructor
  · rw [if_neg (not_lt.mpr (X7_E_le k hk.le))]
  · rw [if_neg (by nlinarith)]

lemma X7_ev3 {a : ℝ} (ha : a < 0) : ∀ᶠ k in atTop,
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a false).val = 1 ∧
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a true).val = 1 := by
  filter_upwards [hbinfty.eventually_gt_atTop (a + c), X7_ev_nat (1/(-a)), X7_ev_nat (1/c)] with k hk h1 h2
  rw [X7_rv_false, X7_rv_true b c k a (hb k).le hc.le, X7_exp_mul_E]
  have h1' : 1 ≤ ((k:ℝ) + 1) * (-a) := by rw [div_le_iff₀ (by linarith)] at h1; linarith
  have h2' : 1 ≤ ((k:ℝ) + 1) * c := by rw [div_le_iff₀ hc] at h2; linarith
  have ee : Real.exp (((k:ℝ) + 1) * a) = X7_E k (-a) := by unfold X7_E; congr 1; ring
  have e1 := X7_E_le_half k h1'
  have e2 := X7_E_le_half k h2'
  have e3 := X7_E_pos k (b k)
  have e4 := X7_E_pos k (-a)
  constructor
  · rw [if_pos (X7_E_lt k (by linarith))]
  · rw [ee, if_pos (by nlinarith)]

lemma X7_ev4 {a : ℝ} (ha : 0 ≤ a) : ∀ᶠ k in atTop,
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a false).val = 1 ∧
    (strictClassicalTest (reverseClassical (twoPointData b c k)) k a true).val = 0 := by
  filter_upwards [hbinfty.eventually_gt_atTop (a + c)] with k hk
  rw [X7_rv_false, X7_rv_true b c k a (hb k).le hc.le, X7_exp_mul_E]
  have hn : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have e1 : 1 ≤ Real.exp (((k:ℝ) + 1) * a) := Real.one_le_exp (by nlinarith)
  have e2 := X7_E_le_one k (hb k).le
  have e3 : X7_E k (b k) ≤ X7_E k c := X7_E_le k (by linarith)
  constructor
  · rw [if_pos (X7_E_lt k (by linarith))]
  · rw [if_neg (by nlinarith)]

end EV

end QAlgorithms.Papers.Independent.Claimed50.P46



namespace QAlgorithms.Papers.Independent.Claimed50.P46

lemma X7_E_tendsto {c : ℝ} (hc : 0 < c) : Tendsto (fun k => X7_E k c) atTop (nhds 0) := by
  have h1 : Tendsto (fun k : ℕ => ((k:ℝ) + 1) * c) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const hc
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  refine h2.congr (fun k => ?_)
  simp only [Function.comp, X7_E]; congr 1; ring

lemma X7_sSup_neg (P : ℝ → Prop) (hP : ∀ a, P a ↔ a < 0) :
    sSup {z : EReal | ∃ a : ℝ, P a ∧ z = (a : EReal)} = 0 := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨a, ha, rfl⟩
    exact_mod_cast ((hP a).mp ha).le
  · apply EReal.ge_of_forall_gt_iff_ge.mp
    intro z hz
    exact le_sSup ⟨z, (hP z).mpr (by exact_mod_cast hz), rfl⟩

section LIM
variable {b : ℕ → ℝ} {c : ℝ} (hb : ∀ k, 0 < b k) (hbinfty : Tendsto b atTop atTop) (hc : 0 < c)
include hb hbinfty hc

lemma X7_limI (a : ℝ) : Tendsto (fun k => blockErrorExponent k
    (testingTypeI (strictClassicalTest (twoPointData b c k) k a))) atTop
    (nhds (if 0 < a then (0 : EReal) else ⊤)) := by
  split_ifs with ha
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [X7_ev2 hb hbinfty hc ha] with k ⟨h1, h2⟩
    rw [X7_typeI b c k (hb k).le, h1, h2]
    rw [show X7_E k (b k) * (1 - 0) + (1 - X7_E k (b k)) * (1 - 0) = 1 by ring,
      ENNReal.ofReal_one, X7_bee_one]
  · refine (EReal.tendsto_coe_atTop.comp hbinfty).congr' ?_
    filter_upwards [X7_ev1 hb hbinfty hc (not_lt.mp ha)] with k ⟨h1, h2⟩
    rw [X7_typeI b c k (hb k).le, h1, h2]
    rw [show X7_E k (b k) * (1 - 0) + (1 - X7_E k (b k)) * (1 - 1) = X7_E k (b k) by ring,
      X7_bee_exp]
    rfl

lemma X7_limII (a : ℝ) : Tendsto (fun k => blockErrorExponent k
    (testingTypeII (testRejection (strictClassicalTest (twoPointData b c k) k a)))) atTop
    (nhds (if 0 < a then (0 : EReal) else (c : EReal))) := by
  split_ifs with ha
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [X7_ev2 hb hbinfty hc ha] with k ⟨h1, h2⟩
    rw [X7_typeIIc b c k hc.le, h1, h2]
    rw [show X7_E k c * (1 - 0) + (1 - X7_E k c) * (1 - 0) = 1 by ring,
      ENNReal.ofReal_one, X7_bee_one]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [X7_ev1 hb hbinfty hc (not_lt.mp ha)] with k ⟨h1, h2⟩
    rw [X7_typeIIc b c k hc.le, h1, h2]
    rw [show X7_E k c * (1 - 0) + (1 - X7_E k c) * (1 - 1) = X7_E k c by ring,
      X7_bee_exp]

lemma X7_limRev (a : ℝ) : Tendsto (fun k =>
    testingTypeI (strictClassicalTest (reverseClassical (twoPointData b c k)) k a)) atTop
    (nhds (if a < 0 then 0 else 1)) := by
  split_ifs with ha
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [X7_ev3 hb hbinfty hc ha] with k ⟨h1, h2⟩
    rw [X7_revTypeI b c k hc.le, h1, h2]
    rw [show X7_E k c * (1 - 1) + (1 - X7_E k c) * (1 - 1) = 0 by ring, ENNReal.ofReal_zero]
  · have ht : Tendsto (fun k => ENNReal.ofReal (1 - X7_E k c)) atTop (nhds 1) := by
      have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1:ℝ))).sub (X7_E_tendsto hc))
      simpa using this
    refine ht.congr' ?_
    filter_upwards [X7_ev4 hb hbinfty hc (not_lt.mp ha)] with k ⟨h1, h2⟩
    rw [X7_revTypeI b c k hc.le, h1, h2]
    congr 1; ring

end LIM

end QAlgorithms.Papers.Independent.Claimed50.P46



namespace QAlgorithms.Papers.Independent.Claimed50.P46

lemma X7_le_limsup {u : ℕ → EReal} {t : EReal} (h : ∀ᶠ k in atTop, t ≤ u k) :
    t ≤ limsup u atTop :=
  (le_liminf_of_le (by isBoundedDefault) h).trans liminf_le_limsup

def X7_T0 (b : ℕ → ℝ) (c : ℝ) (k : ℕ) : SimpleHypothesisTest (.classical (twoPointData b c k)) :=
  fun _ => ⟨0, by norm_num⟩

def X7_T1 (b : ℕ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    SimpleHypothesisTest (.classical (twoPointData b c k)) :=
  show Bool → Set.Icc (0:ℝ) 1 from fun x => if x = true then ⟨1 - X7_E k r, by
      constructor
      · linarith [X7_E_le_one k hr]
      · linarith [X7_E_pos k r]⟩ else ⟨0, by norm_num⟩

section TR
variable {b : ℕ → ℝ} {c : ℝ} (hb : ∀ k, 0 < b k) (hbinfty : Tendsto b atTop atTop) (hc : 0 < c)
include hb hbinfty hc

lemma X7_lower (r : ℝ) (T : (k : ℕ) → SimpleHypothesisTest (.classical (twoPointData b c k)))
    (hT : (r : EReal) ≤ etaL T) : (((min (max r 0) c : ℝ)) : EReal) ≤ zetaUc T := by
  unfold zetaUc zetaU
  rcases le_or_gt r 0 with hr | hr
  · rw [show min (max r 0) c = 0 by rw [max_eq_right hr, min_eq_left hc.le]]
    apply X7_le_limsup
    filter_upwards with k
    apply X7_bee_nonneg
    rw [X7_typeIIc b c k hc.le]
    apply ENNReal.ofReal_le_one.mpr
    have := X7_E_le_one k hc.le
    have := X7_E_pos k c
    nlinarith [(T k false).2.1, (T k false).2.2, (T k true).2.1, (T k true).2.2]
  · rw [max_eq_left hr.le]
    apply EReal.ge_of_forall_gt_iff_ge.mp
    intro t ht
    have ht' : t < min r c := by exact_mod_cast ht
    set t' := (t + min r c) / 2 with ht'def
    have h1 : t < t' := by linarith
    have h2 : t' < r := by linarith [min_le_left r c]
    have h3 : t' < c := by linarith [min_le_right r c]
    have hev : ∀ᶠ k in atTop, (t' : EReal) < blockErrorExponent k (testingTypeI (T k)) :=
      eventually_lt_of_lt_liminf (lt_of_lt_of_le (by exact_mod_cast h2) hT)
    apply X7_le_limsup
    filter_upwards [hev, hbinfty.eventually_ge_atTop 1, X7_ev_nat (2 / (t' - t))] with k hk hbk hn
    have hn' : 2 ≤ ((k:ℝ) + 1) * (t' - t) := by rw [div_le_iff₀ (by linarith)] at hn; linarith
    have hk' : testingTypeI (T k) < ENNReal.ofReal (X7_E k t') := by
      by_contra hcon
      exact absurd (X7_bee_le k (not_lt.mp hcon)) (not_le.mpr hk)
    rw [X7_typeI b c k (hb k).le, ENNReal.ofReal_lt_ofReal_iff (X7_E_pos k t')] at hk'
    apply X7_bee_ge
    rw [X7_typeIIc b c k hc.le]
    apply ENNReal.ofReal_le_ofReal
    have hp : X7_E k (b k) ≤ 1 / 2 := X7_E_le_half k (by
      have : (0:ℝ) ≤ k := by positivity
      nlinarith)
    have hp0 := X7_E_pos k (b k)
    have hq : X7_E k c ≤ X7_E k t' := X7_E_le k h3.le
    have hq1 := X7_E_le_one k hc.le
    have hq0 := X7_E_pos k c
    have hE := X7_exp_mul_E k (t' - t) t'
    rw [show t' - (t' - t) = t by ring] at hE
    have hex : 1 + 2 ≤ Real.exp (((k:ℝ) + 1) * (t' - t)) := by
      linarith [Real.add_one_le_exp (((k:ℝ) + 1) * (t' - t))]
    have ht'0 := X7_E_pos k t'
    have u0 := (T k false).2.1
    have u1 := (T k false).2.2
    have v0 := (T k true).2.1
    have v1 := (T k true).2.2
    rw [← hE]
    nlinarith

lemma X7_upper0 (r : ℝ) (hr : r ≤ 0) :
    (r : EReal) ≤ etaL (P := fun k => .classical (twoPointData b c k)) (X7_T0 b c) ∧
    zetaUc (P := fun k => .classical (twoPointData b c k)) (X7_T0 b c) ≤ (((min (max r 0) c : ℝ)) : EReal) := by
  rw [show min (max r 0) c = 0 by rw [max_eq_right hr, min_eq_left hc.le]]
  constructor
  · apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards with k
    rw [X7_typeI b c k (hb k).le]
    simp only [X7_T0]
    rw [show X7_E k (b k) * (1 - 0) + (1 - X7_E k (b k)) * (1 - 0) = 1 by ring,
      ENNReal.ofReal_one, X7_bee_one]
    exact_mod_cast hr
  · unfold zetaUc zetaU
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards with k
    rw [X7_typeIIc b c k hc.le]
    simp only [X7_T0]
    rw [show X7_E k c * (1 - 0) + (1 - X7_E k c) * (1 - 0) = 1 by ring,
      ENNReal.ofReal_one, X7_bee_one]
    simp

lemma X7_upper1 (r : ℝ) (hr : 0 < r) :
    (r : EReal) ≤ etaL (P := fun k => .classical (twoPointData b c k)) (X7_T1 b c hr.le) ∧
    zetaUc (P := fun k => .classical (twoPointData b c k)) (X7_T1 b c hr.le) ≤ (((min (max r 0) c : ℝ)) : EReal) := by
  rw [max_eq_left hr.le]
  constructor
  · apply EReal.ge_of_forall_gt_iff_ge.mp
    intro t ht
    have ht' : t < r := by exact_mod_cast ht
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [hbinfty.eventually_ge_atTop r, X7_ev_nat (1 / (r - t))] with k hbk hn
    have hn' : 1 ≤ ((k:ℝ) + 1) * (r - t) := by rw [div_le_iff₀ (by linarith)] at hn; linarith
    apply X7_bee_ge
    rw [X7_typeI b c k (hb k).le]
    simp only [X7_T1, if_true, Bool.false_eq_true, if_false]
    apply ENNReal.ofReal_le_ofReal
    have hE := X7_exp_mul_E k (r - t) r
    rw [show r - (r - t) = t by ring] at hE
    have h2 := X7_exp_ge_two k hn'
    have hp : X7_E k (b k) ≤ X7_E k r := X7_E_le k hbk
    have hp0 := X7_E_pos k (b k)
    have hr0 := X7_E_pos k r
    rw [← hE]
    nlinarith
  · unfold zetaUc zetaU
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards with k
    rw [X7_typeIIc b c k hc.le]
    simp only [X7_T1, if_true, Bool.false_eq_true, if_false]
    have hq1 := X7_E_le_one k hc.le
    have hq0 := X7_E_pos k c
    have hr1 := X7_E_le_one k hr.le
    have hr0 := X7_E_pos k r
    rcases min_choice r c with h | h <;> rw [h]
    · apply X7_bee_le; apply ENNReal.ofReal_le_ofReal; nlinarith
    · apply X7_bee_le; apply ENNReal.ofReal_le_ofReal; nlinarith

end TR

end QAlgorithms.Papers.Independent.Claimed50.P46


open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

open QAlgorithms.Papers.Independent.Claimed50.P46 in
theorem solution (b : ℕ → ℝ) (c : ℝ)
    (hb : ∀ k, 0 < b k) (hbinfty : Tendsto b atTop atTop) (hc : 0 < c) :
    let C := twoPointData b c
    let P := fun k => SimpleHypothesisSystem.classical (C k)
    let S := strictClassicalFamily C
    let R := strictClassicalFamily (fun k => reverseClassical (C k))
    (∀ a : ℝ, Tendsto (fun k => blockErrorExponent k (testingTypeI (S.tests a k))) atTop
        (nhds (if 0 < a then (0 : EReal) else ⊤)) ∧
      Tendsto (fun k => blockErrorExponent k (testingTypeII (testRejection (S.tests a k)))) atTop
        (nhds (if 0 < a then (0 : EReal) else (c : EReal)))) ∧
    divergenceL R 0 = 0 ∧ divergenceU R 1 = 0 ∧
    (∀ r : ℝ, correctTradeoff P true false r = ((min (max r 0) c : ℝ) : EReal) ∧
      hanExpression (fun a => etaL (S.tests a)) r = ((max r 0 : ℝ) : EReal)) ∧
    plateauHeight (fun a => zetaUc (S.tests a)) = (c : EReal) ∧
    plateauThreshold (fun a => zetaUc (S.tests a)) = (c : EReal) := by
  intro C P S R
  have hEta : ∀ a, etaL (S.tests a) = if 0 < a then (0 : EReal) else ⊤ :=
    fun a => (X7_limI hb hbinfty hc a).liminf_eq
  have hZeta : ∀ a, zetaUc (S.tests a) = if 0 < a then (0 : EReal) else (c : EReal) :=
    fun a => (X7_limII hb hbinfty hc a).limsup_eq
  have hRU : ∀ a, alphaU (R.tests a) = if a < 0 then 0 else 1 :=
    fun a => (X7_limRev hb hbinfty hc a).limsup_eq
  have hRL : ∀ a, alphaL (R.tests a) = if a < 0 then 0 else 1 :=
    fun a => (X7_limRev hb hbinfty hc a).liminf_eq
  have hH : plateauHeight (fun a => zetaUc (S.tests a)) = (c : EReal) := by
    unfold plateauHeight
    simp only [hZeta]
    apply le_antisymm
    · apply iSup_le
      intro a
      split_ifs
      · exact_mod_cast hc.le
      · exact le_rfl
    · exact le_iSup_of_le 0 (by simp)
  refine ⟨fun a => ⟨X7_limI hb hbinfty hc a, X7_limII hb hbinfty hc a⟩, ?_, ?_,
    fun r => ⟨?_, ?_⟩, hH, ?_⟩
  · unfold divergenceL
    apply X7_sSup_neg
    intro a; rw [hRU a]; split_ifs with h <;> simp [h]
  · unfold divergenceU
    apply X7_sSup_neg
    intro a; rw [hRL a]; split_ifs with h <;> simp [h]
  · unfold correctTradeoff
    simp only [if_true, Bool.false_eq_true, if_false]
    apply le_antisymm
    · rcases le_or_gt r 0 with hr | hr
      · obtain ⟨h1, h2⟩ := X7_upper0 hb hbinfty hc r hr
        refine le_trans (sInf_le ?_) h2
        exact ⟨X7_T0 b c, h1, rfl⟩
      · obtain ⟨h1, h2⟩ := X7_upper1 hb hbinfty hc r hr
        refine le_trans (sInf_le ?_) h2
        exact ⟨X7_T1 b c hr.le, h1, rfl⟩
    · apply le_sInf
      rintro _ ⟨T, hT, rfl⟩
      exact X7_lower hb hbinfty hc r T hT
  · unfold hanExpression
    simp only [hEta]
    have hm : max (0 : EReal) (r : EReal) = ((max r 0 : ℝ) : EReal) := by
      rcases le_total r 0 with h | h
      · rw [max_eq_left (by exact_mod_cast h), max_eq_right h]; rfl
      · rw [max_eq_right (by exact_mod_cast h), max_eq_left h]
    apply le_antisymm
    · apply EReal.le_of_forall_lt_iff_le.mp
      intro z hz
      have hz' : max r 0 < z := by exact_mod_cast hz
      refine iInf_le_of_le (z - max r 0) ?_
      rw [if_pos (by linarith), hm, ← EReal.coe_add]
      exact_mod_cast (by linarith : z - max r 0 + max r 0 ≤ z)
    · apply le_iInf
      intro a
      split_ifs with h
      · rw [hm, ← EReal.coe_add]
        exact_mod_cast (by linarith : max r 0 ≤ a + max r 0)
      · simp
  · unfold plateauThreshold
    rw [hH]
    simp only [hZeta]
    apply le_antisymm
    · exact sInf_le ⟨0, by simp, by simp⟩
    · apply le_sInf
      rintro _ ⟨a, ha, rfl⟩
      split_ifs at ha with h
      · exact absurd (by exact_mod_cast ha : (0:ℝ) = c) hc.ne
      · rw [← EReal.coe_sub]
        exact_mod_cast (by linarith : c ≤ c - a)
