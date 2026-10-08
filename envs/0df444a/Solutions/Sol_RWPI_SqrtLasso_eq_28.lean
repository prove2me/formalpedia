-- Prove2me | solution 1 for RWPI.SqrtLasso.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T08:41:00.142255+00:00
-- url     : https://prove2.me/submissions/253d1c55-ae7e-47b7-977d-6612668bbc32

import Definitions.Def_RWPI_SqrtLasso_lqSqCost
import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Mathlib

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators

lemma holder_toReal (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) : p.toReal.HolderConjugate q.toReal := by
  have : p.HolderConjugate q := hpq
  refine ⟨?_, ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp,
    ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq⟩
  have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
  simpa [ENNReal.toReal_add, ENNReal.inv_ne_top,
    ENNReal.HolderConjugate.ne_zero p q, ENNReal.HolderConjugate.ne_zero q p] using h

lemma dot_abs_le_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  rw [PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp),
    PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq)]
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ _ := by
      simpa using Real.inner_le_Lp_mul_Lq Finset.univ (fun j => |x j|)
        (fun j => |y j|) (holder_toReal p q hpq hp hq)

lemma dot_abs_le_one_top {d : ℕ} (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp ⊤ y‖ := by
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ ∑ j, |x j| * ‖WithLp.toLp ⊤ y‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using PiLp.norm_apply_le (WithLp.toLp ⊤ y) j
    _ = _ := by
      rw [← Finset.sum_mul, PiLp.norm_eq_of_L1]
      simp

lemma dot_abs_le {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact dot_abs_le_one_top x y
  · exact dot_abs_le_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x y

#print axioms dot_abs_le_one_top
#print axioms dot_abs_le
#print axioms holder_toReal
#print axioms dot_abs_le_finite
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators NNReal

lemma norming_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let f : Fin d → ℝ≥0 := fun j => ⟨|x j|, abs_nonneg _⟩
  have hc := holder_toReal p q hpq hp hq
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp Finset.univ f hc).1
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then (g j : ℝ) else -(g j : ℝ)
  have hy (j : Fin d) : |y j| = (g j : ℝ) := by
    dsimp [y]
    split_ifs <;> simp
  have hxy (j : Fin d) : x j * y j = |x j| * (g j : ℝ) := by
    dsimp [y]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_eq_sum hc.symm.pos]
    simp only [Real.norm_eq_abs, hy]
    have hbound := NNReal.rpow_le_one hg (one_div_nonneg.mpr hc.symm.nonneg)
    exact_mod_cast hbound
  · rw [PiLp.norm_eq_sum hc.pos]
    simp only [Real.norm_eq_abs]
    simp_rw [hxy]
    have heR := congrArg (fun z : ℝ≥0 => (z : ℝ)) he
    have hf (j : Fin d) : (f j : ℝ) = |x j| := rfl
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow, hf] using heR

lemma norming_one_top {d : ℕ} (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp ⊤ y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp 1 x‖ := by
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then 1 else -1
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    dsimp [y]
    split_ifs <;> norm_num
  · rw [PiLp.norm_eq_of_L1]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [y]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]

lemma norming {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact norming_one_top x
  · exact norming_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x

lemma norming_unit_of_positive {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) (hx : 0 < ‖WithLp.toLp p x‖) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ = 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  obtain ⟨y, hy, hxy⟩ := norming p q hq hpq x
  refine ⟨y, le_antisymm hy ?_, hxy⟩
  have hbound := dot_abs_le p q hq hpq x y
  rw [hxy, abs_of_pos hx] at hbound
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) hx

#print axioms norming_one_top
#print axioms norming
#print axioms norming_unit_of_positive
#print axioms norming_finite
end TransportCodex

set_option autoImplicit false
namespace TransportCodex

lemma completed_square (a b γ t : ℝ) (hγ : b ^ 2 < γ) :
    (a + b * t) ^ 2 - γ * t ^ 2 =
      γ * a ^ 2 / (γ - b ^ 2) -
        (γ - b ^ 2) * (t - a * b / (γ - b ^ 2)) ^ 2 := by
  have hd : γ - b ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr hγ)
  field_simp
  ring

lemma quadratic_le (a b γ t : ℝ) (hγ : b ^ 2 < γ) :
    (a + b * t) ^ 2 - γ * t ^ 2 ≤ γ * a ^ 2 / (γ - b ^ 2) := by
  rw [completed_square a b γ t hγ]
  exact sub_le_self _ (mul_nonneg (le_of_lt (sub_pos.mpr hγ)) (sq_nonneg _))

lemma quadratic_sup_of_strict (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ : b ^ 2 < γ) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - γ * t ^ 2)) =
      ENNReal.ofReal (γ * a ^ 2 / (γ - b ^ 2)) := by
  apply le_antisymm
  · refine iSup_le fun t => iSup_le fun _ => ?_
    exact ENNReal.ofReal_le_ofReal (quadratic_le a b γ t hγ)
  · have ht : 0 ≤ a * b / (γ - b ^ 2) :=
      div_nonneg (mul_nonneg ha hb) (le_of_lt (sub_pos.mpr hγ))
    have he := completed_square a b γ (a * b / (γ - b ^ 2)) hγ
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at he
    rw [← he]
    exact le_iSup_of_le (a * b / (γ - b ^ 2)) (le_iSup_of_le ht le_rfl)

lemma quadratic_sup_eq_top_of_unbounded (a b γ : ℝ)
    (hu : ∀ R : ℝ, 0 ≤ R → ∃ t : ℝ, 0 ≤ t ∧
      R < (a + b * t) ^ 2 - γ * t ^ 2) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - γ * t ^ 2)) = ⊤ := by
  apply iSup_eq_top.mpr
  intro B hB
  obtain ⟨t, ht, hgt⟩ := hu (B.toReal + 1) (by positivity)
  refine ⟨t, lt_of_lt_of_le ?_ (le_iSup_of_le ht le_rfl)⟩
  apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hB)).mpr
  linarith

lemma quadratic_sup_boundary_zero (a b : ℝ) (hab : a * b = 0) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - b ^ 2 * t ^ 2)) =
      ENNReal.ofReal (a ^ 2) := by
  have he (t : ℝ) : (a + b * t) ^ 2 - b ^ 2 * t ^ 2 = a ^ 2 := by
    have hz : a * b * t = 0 := by rw [hab, zero_mul]
    nlinarith
  simp_rw [he]
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun _ => le_rfl
  · exact le_iSup_of_le (0 : ℝ) (le_iSup_of_le (le_refl 0) le_rfl)

lemma quadratic_sup_boundary_positive (a b : ℝ) (hab : 0 < a * b) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - b ^ 2 * t ^ 2)) = ⊤ := by
  apply quadratic_sup_eq_top_of_unbounded
  intro R hR
  have hd : 0 < 2 * a * b := by nlinarith
  refine ⟨(R + 1) / (2 * a * b), div_nonneg (by linarith) hd.le, ?_⟩
  have he : 2 * a * b * ((R + 1) / (2 * a * b)) = R + 1 := by
    field_simp [hab.ne']
    exact div_self (ne_of_gt hab)
  nlinarith [sq_nonneg a]

lemma quadratic_sup_below (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ : γ < b ^ 2) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - γ * t ^ 2)) = ⊤ := by
  apply quadratic_sup_eq_top_of_unbounded
  intro R hR
  let d := b ^ 2 - γ
  have hd : 0 < d := sub_pos.mpr hγ
  let t := (R + 1) / d + 1
  have ht1 : 1 ≤ t := by
    have hfrac : 0 ≤ (R + 1) / d := div_nonneg (by linarith) hd.le
    dsimp [t]
    linarith
  have ht : 0 ≤ t := by linarith
  have he : d * ((R + 1) / d) = R + 1 := by
    field_simp
  have hdt : d * t = R + 1 + d := by dsimp [t]; nlinarith
  have hs : 0 ≤ t ^ 2 - t := by nlinarith
  have hds := mul_nonneg hd.le hs
  have habt := mul_nonneg (mul_nonneg ha hb) ht
  refine ⟨t, ht, ?_⟩
  dsimp [d] at hdt hds hd
  nlinarith [sq_nonneg a]

theorem quadratic_sup_closed_form (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal ((a + b * t) ^ 2 - γ * t ^ 2)) =
      if b ^ 2 < γ then ENNReal.ofReal (γ * a ^ 2 / (γ - b ^ 2))
      else if γ = b ^ 2 ∧ a * b = 0 then ENNReal.ofReal (a ^ 2) else ⊤ := by
  split_ifs with hstrict hzero
  · exact quadratic_sup_of_strict a b γ ha hb hstrict
  · rcases hzero with ⟨rfl, hab⟩
    exact quadratic_sup_boundary_zero a b hab
  · by_cases he : γ = b ^ 2
    · subst γ
      have hab : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha hb)
        (by intro hz; exact hzero ⟨rfl, hz.symm⟩)
      exact quadratic_sup_boundary_positive a b hab
    · exact quadratic_sup_below a b γ ha hb (lt_of_le_of_ne (le_of_not_gt hstrict) he)

#print axioms quadratic_sup_boundary_zero
#print axioms quadratic_sup_boundary_positive
#print axioms quadratic_sup_below
#print axioms quadratic_sup_closed_form

#print axioms completed_square
#print axioms quadratic_sup_of_strict
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators

lemma displacement_sup_le_scalar {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (β : Fin d → ℝ) (r γ : ℝ) :
    (⨆ h : Fin d → ℝ, ENNReal.ofReal
      ((r - ∑ j, β j * h j) ^ 2 - γ * ‖WithLp.toLp q h‖ ^ 2)) ≤
    ⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal
      ((|r| + ‖WithLp.toLp p β‖ * t) ^ 2 - γ * t ^ 2) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  refine iSup_le fun h => ?_
  have hb := dot_abs_le p q hq hpq β h
  have ht : |r - ∑ j, β j * h j| ≤ |r| + |∑ j, β j * h j| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le r 0 (∑ j, β j * h j)
  have hab : |r - ∑ j, β j * h j| ≤ |r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖ :=
    ht.trans (add_le_add le_rfl hb)
  have hs : (r - ∑ j, β j * h j) ^ 2 ≤
      (|r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖) ^ 2 := by
    have hpos : 0 ≤ |r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖ := by positivity
    nlinarith [sq_abs (r - ∑ j, β j * h j), abs_nonneg (r - ∑ j, β j * h j),
      abs_nonneg r, norm_nonneg (WithLp.toLp p β), norm_nonneg (WithLp.toLp q h)]
  apply le_trans (ENNReal.ofReal_le_ofReal (sub_le_sub_right hs _))
  exact le_iSup_of_le ‖WithLp.toLp q h‖ (le_iSup_of_le (norm_nonneg (WithLp.toLp q h)) le_rfl)

lemma displacement_sup_eq_scalar_of_positive {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (β : Fin d → ℝ) (r γ : ℝ)
    (hβ : 0 < ‖WithLp.toLp p β‖) :
    (⨆ h : Fin d → ℝ, ENNReal.ofReal
      ((r - ∑ j, β j * h j) ^ 2 - γ * ‖WithLp.toLp q h‖ ^ 2)) =
    ⨆ (t : ℝ) (_ : 0 ≤ t), ENNReal.ofReal
      ((|r| + ‖WithLp.toLp p β‖ * t) ^ 2 - γ * t ^ 2) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨v, hv, hdot⟩ := norming_unit_of_positive p q hq hpq β hβ
  apply le_antisymm (displacement_sup_le_scalar p q hq hpq β r γ)
  refine iSup_le fun t => iSup_le fun ht => ?_
  let ε : ℝ := if 0 ≤ r then 1 else -1
  let h : Fin d → ℝ := (-ε * t) • v
  have hn : ‖WithLp.toLp q h‖ = t := by
    change ‖(-ε * t) • WithLp.toLp q v‖ = t
    rw [norm_smul, hv, Real.norm_eq_abs, mul_one]
    dsimp [ε]
    split_ifs <;> simp [abs_of_nonneg ht]
  have hsum : ∑ j, β j * h j = (-ε * t) * ‖WithLp.toLp p β‖ := by
    dsimp [h]
    rw [← hdot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : (r - ∑ j, β j * h j) ^ 2 = (|r| + ‖WithLp.toLp p β‖ * t) ^ 2 := by
    rw [hsum]
    dsimp [ε]
    split_ifs with hr
    · rw [abs_of_nonneg hr]
      ring
    · rw [abs_of_neg (lt_of_not_ge hr)]
      ring
  apply le_iSup_of_le h
  rw [hn, he]

lemma displacement_sup_of_zero_norm {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (β : Fin d → ℝ) (r γ : ℝ) (hγ : 0 ≤ γ)
    (hβ : ‖WithLp.toLp p β‖ = 0) :
    (⨆ h : Fin d → ℝ, ENNReal.ofReal
      ((r - ∑ j, β j * h j) ^ 2 - γ * ‖WithLp.toLp q h‖ ^ 2)) =
      ENNReal.ofReal (r ^ 2) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  apply le_antisymm
  · refine iSup_le fun h => ?_
    have hd := dot_abs_le p q hq hpq β h
    rw [hβ, zero_mul] at hd
    have hdot : ∑ j, β j * h j = 0 := abs_nonpos_iff.mp hd
    rw [hdot, sub_zero]
    exact ENNReal.ofReal_le_ofReal (sub_le_self _ (mul_nonneg hγ (sq_nonneg _)))
  · apply le_iSup_of_le (0 : Fin d → ℝ)
    simp

lemma norm_zero_iff {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) : ‖WithLp.toLp p β‖ = 0 ↔ β = 0 := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  constructor
  · intro h
    have he := congrArg (fun x : WithLp p (Fin d → ℝ) => WithLp.ofLp x) (norm_eq_zero.mp h)
    simpa using he
  · rintro rfl
    simp

#print axioms displacement_sup_of_zero_norm
#print axioms norm_zero_iff

#print axioms displacement_sup_le_scalar
#print axioms displacement_sup_eq_scalar_of_positive
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators
open RWPI.SqrtLasso

def unstack {d : ℕ} (v : Fin (d + 1) → ℝ) : (Fin d → ℝ) × ℝ :=
  (Fin.init v, v (Fin.last d))

lemma stack_unstack {d : ℕ} (v : Fin (d + 1) → ℝ) : stack (unstack v) = v :=
  Fin.snoc_init_self v

lemma betaBar_dot_stack {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) :
    ∑ j, betaBar β j * stack z j = z.2 - ∑ j, β j * z.1 j := by
  rw [Fin.sum_univ_castSucc]
  simp [betaBar, stack, Finset.sum_neg_distrib]
  ring

lemma betaBar_ne_zero {d : ℕ} (β : Fin d → ℝ) : betaBar β ≠ 0 := by
  intro h
  have he := congrFun h (Fin.last d)
  simpa [betaBar, stack] using he

lemma phi_lq_eq_displacement_sup {d : ℕ} (q : ENNReal) (hq : 1 ≤ q)
    (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    phi (lqSqCost q) (squareLoss β) γ z =
      ⨆ h : Fin (d + 1) → ℝ, ENNReal.ofReal
        ((∑ j, betaBar β j * stack z j - ∑ j, betaBar β j * h j) ^ 2 -
          γ * ‖WithLp.toLp q h‖ ^ 2) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have he (u : (Fin d → ℝ) × ℝ) :
      ENNReal.ofReal (squareLoss β u) - ENNReal.ofReal γ * lqSqCost q u z =
      ENNReal.ofReal
        ((∑ j, betaBar β j * stack z j -
          ∑ j, betaBar β j * (stack z - stack u) j) ^ 2 -
          γ * ‖WithLp.toLp q (stack z - stack u)‖ ^ 2) := by
    have hn : ‖WithLp.toLp q (stack u - stack z)‖ =
        ‖WithLp.toLp q (stack z - stack u)‖ := by
      have hs : stack u - stack z = -(stack z - stack u) := by abel
      rw [hs]
      change ‖-WithLp.toLp q (stack z - stack u)‖ = _
      exact norm_neg _
    have hl : (∑ j, betaBar β j * stack z j -
        ∑ j, betaBar β j * (stack z - stack u) j) =
        u.2 - ∑ j, β j * u.1 j := by
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [betaBar_dot_stack β u]
      ring
    rw [hl, lqSqCost, hn,
      ← ENNReal.ofReal_mul hγ, ← ENNReal.ofReal_sub _ (mul_nonneg hγ (sq_nonneg _))]
    rfl
  unfold phi
  apply le_antisymm
  · refine iSup_le fun u => iSup_le fun _ => ?_
    rw [he]
    apply le_iSup_of_le (stack z - stack u)
    exact le_rfl
  · refine iSup_le fun h => ?_
    let u := unstack (stack z - h)
    have hs : stack z - stack u = h := by
      rw [show stack u = stack z - h from stack_unstack _]
      abel
    apply le_iSup_of_le u
    apply le_iSup_of_le (by simp [lqSqCost] : lqSqCost q u z ≠ ⊤)
    rw [he, hs]

#print axioms stack_unstack
#print axioms betaBar_dot_stack
#print axioms betaBar_ne_zero
#print axioms phi_lq_eq_displacement_sup
end TransportCodex

set_option autoImplicit false
open scoped BigOperators
open RWPI.SqrtLasso

theorem solution {d : ℕ} (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    phi (lqSqCost q) (squareLoss β) γ z =
      if ‖WithLp.toLp p (betaBar β)‖ ^ 2 < γ then
        ENNReal.ofReal ((∑ j, betaBar β j * stack z j) ^ 2 * γ /
          (γ - ‖WithLp.toLp p (betaBar β)‖ ^ 2))
      else if γ = ‖WithLp.toLp p (betaBar β)‖ ^ 2 ∧ ∑ j, betaBar β j * stack z j = 0 then 0
      else ⊤ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hb : 0 < ‖WithLp.toLp p (betaBar β)‖ := lt_of_le_of_ne (norm_nonneg _)
    (by
      intro h
      exact TransportCodex.betaBar_ne_zero β
        ((TransportCodex.norm_zero_iff p q hpq (betaBar β)).mp h.symm))
  rw [TransportCodex.phi_lq_eq_displacement_sup q hq.le β z γ hγ,
    TransportCodex.displacement_sup_eq_scalar_of_positive p q hq hpq (betaBar β) _ γ hb,
    TransportCodex.quadratic_sup_closed_form _ _ _ (abs_nonneg _) (norm_nonneg _)]
  have hz : |∑ j, betaBar β j * stack z j| * ‖WithLp.toLp p (betaBar β)‖ = 0 ↔
      ∑ j, betaBar β j * stack z j = 0 := by
    rw [mul_eq_zero, abs_eq_zero]
    simp [ne_of_gt hb]
  simp only [hz, sq_abs]
  split_ifs with hgt hboundary
  · congr 1
    ring
  · simp [hboundary.2]
  · rfl

#print axioms solution
