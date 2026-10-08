-- Prove2me | solution 1 for RWPI.SqrtLasso.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T08:22:15.090258+00:00
-- url     : https://prove2.me/submissions/3500d1b6-0745-4e42-9050-cb5d059b797f

import Definitions.Def_RWPI_SqrtLasso_MSE
import Definitions.Def_RWPI_SqrtLasso_Nq
import Definitions.Def_RWPI_SqrtLasso_phi
import Definitions.Def_RWPI_SqrtLasso_squareLoss
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Mathlib
import Theorems.Thm_RWPI_SqrtLasso_eq_29_minimization

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory

lemma coupling_integral_bound {Z : Type*} [MeasurableSpace Z]
    (P Q : Measure Z) (π : Measure (Z × Z)) (hf : π.map Prod.fst = P)
    (hs : π.map Prod.snd = Q) (f : Z → ENNReal) (hfm : Measurable f)
    (c : Z → Z → ENNReal) (κ K : ENNReal) (hκ : κ ≠ ⊤)
    (hpoint : ∀ z w, f z ≤ κ * c z w + K * f w) :
    (∫⁻ z, f z ∂P) ≤ κ * (∫⁻ z, c z.1 z.2 ∂π) + K * (∫⁻ w, f w ∂Q) := by
  rw [← hf, ← hs, lintegral_map hfm measurable_fst, lintegral_map hfm measurable_snd]
  apply le_trans (lintegral_mono (fun z : Z × Z => hpoint z.1 z.2))
  have hfs : Measurable (fun z : Z × Z => f z.2) := hfm.comp measurable_snd
  have hg : Measurable (fun z : Z × Z => K * f z.2) :=
    measurable_const.mul (hfm.comp measurable_snd)
  rw [lintegral_add_right (fun z : Z × Z => κ * c z.1 z.2) hg,
    lintegral_const_mul' κ _ hκ, lintegral_const_mul K hfs]

#print axioms coupling_integral_bound
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory

lemma transport_infimum_bound {Z : Type*} [MeasurableSpace Z]
    (c : Z → Z → ENNReal) (P Q : Measure Z) (a κ C : ENNReal)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤)
    (h : ∀ π : Measure (Z × Z),
      IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q →
      a ≤ κ * (∫⁻ z, c z.1 z.2 ∂π) + C) :
    a ≤ κ * RWPI.SqrtLasso.transportCost c P Q + C := by
  unfold RWPI.SqrtLasso.transportCost
  rw [ENNReal.mul_iInf_of_ne hκ0 hκtop, ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hκ0 hκtop, ENNReal.iInf_add]
  exact le_iInf fun hc => h π hc

lemma worstCase_upper_of_coupling_bound {Z : Type*} [MeasurableSpace Z]
    (c : Z → Z → ENNReal) (Q : Measure Z) (l : Z → ℝ) (δ : ℝ) (κ C : ENNReal)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤)
    (h : ∀ P : Measure Z, IsProbabilityMeasure P → ∀ π : Measure (Z × Z),
      IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q →
      (∫⁻ z, ENNReal.ofReal (l z) ∂P) ≤ κ * (∫⁻ z, c z.1 z.2 ∂π) + C) :
    RWPI.SqrtLasso.worstCase c δ Q l ≤ κ * ENNReal.ofReal δ + C := by
  unfold RWPI.SqrtLasso.worstCase
  refine iSup_le fun P => iSup_le fun hP => ?_
  apply le_trans (transport_infimum_bound c P Q _ κ C hκ0 hκtop (h P hP.1))
  gcongr
  exact hP.2

#print axioms transport_infimum_bound
#print axioms worstCase_upper_of_coupling_bound
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators
open RWPI.SqrtLasso

lemma phi_Nq_eq_predictor_sup {d : ℕ} (q : ENNReal) (β : Fin d → ℝ)
    (z : (Fin d → ℝ) × ℝ) (γ : ℝ) :
    phi (fun u w => Nq q u w ^ 2) (squareLoss β) γ z =
      ⨆ x : Fin d → ℝ, ENNReal.ofReal (squareLoss β (x, z.2)) -
        ENNReal.ofReal γ * (ENNReal.ofReal ‖WithLp.toLp q (x - z.1)‖) ^ 2 := by
  unfold phi
  apply le_antisymm
  · refine iSup_le fun u => iSup_le fun hu => ?_
    have hy : u.2 = z.2 := by
      by_contra hn
      simp [Nq, hn] at hu
    have he : u = (u.1, z.2) := Prod.ext rfl hy
    rw [he]
    simp only [Nq, ite_true]
    exact le_iSup
      (fun x : Fin d → ℝ => ENNReal.ofReal (squareLoss β (x, z.2)) -
        ENNReal.ofReal γ * (ENNReal.ofReal ‖WithLp.toLp q (x - z.1)‖) ^ 2) u.1
  · refine iSup_le fun x => ?_
    have hc : Nq q (x, z.2) z ^ 2 ≠ ⊤ := by simp [Nq]
    apply le_iSup_of_le (x, z.2)
    apply le_iSup_of_le hc
    simp only [Nq, ite_true, le_refl]

#print axioms phi_Nq_eq_predictor_sup
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators
open RWPI.SqrtLasso

lemma squareLoss_displacement {d : ℕ} (β : Fin d → ℝ)
    (z : (Fin d → ℝ) × ℝ) (x : Fin d → ℝ) :
    squareLoss β (x, z.2) =
      (z.2 - ∑ j, β j * z.1 j - ∑ j, β j * (x - z.1) j) ^ 2 := by
  unfold squareLoss
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

lemma phi_Nq_eq_displacement_sup {d : ℕ} (q : ENNReal) (hq : 1 ≤ q) (β : Fin d → ℝ)
    (z : (Fin d → ℝ) × ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    phi (fun u w => Nq q u w ^ 2) (squareLoss β) γ z =
      ⨆ h : Fin d → ℝ, ENNReal.ofReal
        ((z.2 - ∑ j, β j * z.1 j - ∑ j, β j * h j) ^ 2 -
          γ * ‖WithLp.toLp q h‖ ^ 2) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  rw [phi_Nq_eq_predictor_sup]
  have he (x : Fin d → ℝ) :
      ENNReal.ofReal (squareLoss β (x, z.2)) -
        ENNReal.ofReal γ * (ENNReal.ofReal ‖WithLp.toLp q (x - z.1)‖) ^ 2 =
      ENNReal.ofReal
        ((z.2 - ∑ j, β j * z.1 j - ∑ j, β j * (x - z.1) j) ^ 2 -
          γ * ‖WithLp.toLp q (x - z.1)‖ ^ 2) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hγ (sq_nonneg _)),
      ENNReal.ofReal_mul hγ, ENNReal.ofReal_pow (norm_nonneg (WithLp.toLp q (x - z.1))) 2,
      squareLoss_displacement]
  simp_rw [he]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    exact le_iSup (fun h : Fin d → ℝ => ENNReal.ofReal
      ((z.2 - ∑ j, β j * z.1 j - ∑ j, β j * h j) ^ 2 -
        γ * ‖WithLp.toLp q h‖ ^ 2)) (x - z.1)
  · refine iSup_le fun h => ?_
    apply le_iSup_of_le (z.1 + h)
    have hs : z.1 + h - z.1 = h := by abel
    rw [hs]

#print axioms squareLoss_displacement
#print axioms phi_Nq_eq_displacement_sup
end TransportCodex

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

lemma squareLoss_pointwise_upper {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (β : Fin d → ℝ) (γ : ℝ)
    (hγ : ‖WithLp.toLp p β‖ ^ 2 < γ) (z w : (Fin d → ℝ) × ℝ) :
    ENNReal.ofReal (squareLoss β z) ≤
      ENNReal.ofReal γ * (Nq q z w ^ 2) +
        ENNReal.ofReal (γ / (γ - ‖WithLp.toLp p β‖ ^ 2)) *
          ENNReal.ofReal (squareLoss β w) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hγpos : 0 < γ := lt_of_le_of_lt (sq_nonneg _) hγ
  have hden : 0 < γ - ‖WithLp.toLp p β‖ ^ 2 := sub_pos.mpr hγ
  by_cases hy : z.2 = w.2
  · have hz : z = (z.1, w.2) := Prod.ext rfl hy
    rw [hz]
    let r : ℝ := w.2 - ∑ j, β j * w.1 j
    let h : Fin d → ℝ := z.1 - w.1
    have hdot := dot_abs_le p q hq hpq β h
    have hab : |r - ∑ j, β j * h j| ≤ |r| + |∑ j, β j * h j| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le r 0 (∑ j, β j * h j)
    have he : |r - ∑ j, β j * h j| ≤ |r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖ :=
      hab.trans (add_le_add le_rfl hdot)
    have hs : (r - ∑ j, β j * h j) ^ 2 ≤
        (|r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖) ^ 2 := by
      have hp : 0 ≤ |r| + ‖WithLp.toLp p β‖ * ‖WithLp.toLp q h‖ := by positivity
      nlinarith [sq_abs (r - ∑ j, β j * h j), abs_nonneg (r - ∑ j, β j * h j)]
    have hu := quadratic_le |r| ‖WithLp.toLp p β‖ γ ‖WithLp.toLp q h‖ hγ
    rw [sq_abs] at hu
    have hreal : squareLoss β (z.1, w.2) ≤
        γ * ‖WithLp.toLp q h‖ ^ 2 +
          γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * squareLoss β w := by
      rw [squareLoss_displacement β w z.1]
      change (r - ∑ j, β j * h j) ^ 2 ≤
        γ * ‖WithLp.toLp q h‖ ^ 2 + γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * r ^ 2
      have hfrac : γ * r ^ 2 / (γ - ‖WithLp.toLp p β‖ ^ 2) =
          γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * r ^ 2 := by ring
      rw [hfrac] at hu
      linarith
    have hcoef : 0 ≤ γ / (γ - ‖WithLp.toLp p β‖ ^ 2) := div_nonneg hγpos.le hden.le
    have hc : 0 ≤ γ * ‖WithLp.toLp q h‖ ^ 2 := mul_nonneg hγpos.le (sq_nonneg _)
    have hloss : 0 ≤ squareLoss β w := by unfold squareLoss; positivity
    have hcalc : ENNReal.ofReal
        (γ * ‖WithLp.toLp q h‖ ^ 2 + γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * squareLoss β w) =
      ENNReal.ofReal γ * (Nq q (z.1, w.2) w ^ 2) +
        ENNReal.ofReal (γ / (γ - ‖WithLp.toLp p β‖ ^ 2)) * ENNReal.ofReal (squareLoss β w) := by
      rw [ENNReal.ofReal_add hc (mul_nonneg hcoef hloss),
        ENNReal.ofReal_mul hγpos.le, ENNReal.ofReal_mul hcoef,
        ENNReal.ofReal_pow (norm_nonneg (WithLp.toLp q h)) 2]
      simp only [Nq, ite_true]
      rfl
    exact (ENNReal.ofReal_le_ofReal hreal).trans_eq hcalc

  · have hg : ENNReal.ofReal γ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hγpos)
    simp [Nq, hy, hg]

#print axioms squareLoss_pointwise_upper
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open WassersteinDRO.Regularization

lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma transportCost_le_empirical_cost {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {n : ℕ} (hn : 0 < n) (X Y : Fin n → Z)
    (c : Z → Z → ENNReal) :
    RWPI.SqrtLasso.transportCost c (empiricalDistribution X) (empiricalDistribution Y) ≤
      (n : ENNReal)⁻¹ * ∑ i, c (X i) (Y i) := by
  unfold RWPI.SqrtLasso.transportCost
  apply iInf_le_of_le (empiricalDistribution (fun i => (X i, Y i)))
  apply iInf_le_of_le (empirical_coupling hn X Y)
  exact le_of_eq (empirical_lintegral _ _)

#print axioms transportCost_le_empirical_cost
#print axioms empirical_coupling
#print axioms empirical_probability
#print axioms empirical_map
#print axioms empirical_lintegral
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma squareLoss_measurable {d : ℕ} (β : Fin d → ℝ) :
    Measurable (fun z : (Fin d → ℝ) × ℝ => ENNReal.ofReal (squareLoss β z)) := by
  apply ENNReal.measurable_ofReal.comp
  unfold squareLoss
  fun_prop

lemma empirical_squareLoss {d n : ℕ} (hn : 0 < n)
    (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (β : Fin d → ℝ) :
    (∫⁻ z, ENNReal.ofReal (squareLoss β z)
      ∂empiricalDistribution (fun i => (X i, Y i))) = ENNReal.ofReal (MSE X Y β) := by
  rw [empirical_lintegral]
  unfold MSE
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)⁻¹),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by unfold squareLoss; positivity)]

#print axioms squareLoss_measurable
#print axioms empirical_squareLoss
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators
open RWPI.SqrtLasso

lemma mse_nonneg {d n : ℕ} (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (β : Fin d → ℝ) :
    0 ≤ MSE X Y β := by
  unfold MSE squareLoss
  positivity

lemma mean_sq_scale {n : ℕ} (r : Fin n → ℝ) (M δ : ℝ) (hM : 0 < M) (hδ : 0 ≤ δ)
    (hmean : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = M) :
    (n : ℝ)⁻¹ * ∑ i, (Real.sqrt δ * r i / Real.sqrt M) ^ 2 = δ := by
  have hs : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM.le
  have hd : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ
  have hm : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  have he (i : Fin n) : (Real.sqrt δ * r i / Real.sqrt M) ^ 2 = δ / M * (r i) ^ 2 := by
    rw [div_pow, mul_pow, hs, hd]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    (n : ℝ)⁻¹ * (δ / M * ∑ i, r i ^ 2) = δ / M * ((n : ℝ)⁻¹ * ∑ i, r i ^ 2) := by ring
    _ = δ / M * M := by rw [hmean]
    _ = δ := div_mul_cancel₀ _ hM.ne'

lemma mean_sq_loss_scale {n : ℕ} (r : Fin n → ℝ) (M δ b : ℝ) (hM : 0 < M)
    (hmean : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = M) :
    (n : ℝ)⁻¹ * ∑ i, (r i + b * (Real.sqrt δ * r i / Real.sqrt M)) ^ 2 =
      (Real.sqrt M + b * Real.sqrt δ) ^ 2 := by
  have hs : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM.le
  have hm : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  have he (i : Fin n) :
      (r i + b * (Real.sqrt δ * r i / Real.sqrt M)) ^ 2 =
      ((Real.sqrt M + b * Real.sqrt δ) / Real.sqrt M) ^ 2 * (r i) ^ 2 := by
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    (n : ℝ)⁻¹ * (((Real.sqrt M + b * Real.sqrt δ) / Real.sqrt M) ^ 2 * ∑ i, r i ^ 2) =
        ((Real.sqrt M + b * Real.sqrt δ) / Real.sqrt M) ^ 2 * M := by
      rw [← hmean]
      ring
    _ = (Real.sqrt M + b * Real.sqrt δ) ^ 2 := by
      rw [div_pow, hs, div_mul_cancel₀ _ hM.ne']

lemma mean_sq_zero {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ)
    (hmean : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = 0) : ∀ i, r i = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, (r i) ^ 2 = 0 :=
    (mul_eq_zero.mp hmean).resolve_left (inv_ne_zero hnR)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (r i))).mp hs
  intro i
  exact sq_eq_zero_iff.mp (hz i (Finset.mem_univ i))

lemma mean_constant {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n : ℝ)⁻¹ * ∑ _i : Fin n, a = a := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [hnR]

lemma mean_sq_constant_cost {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 ≤ δ) :
    (n : ℝ)⁻¹ * ∑ _i : Fin n, (Real.sqrt δ) ^ 2 = δ := by
  simp_rw [Real.sq_sqrt hδ]
  exact mean_constant hn δ

lemma mean_sq_zero_loss {n : ℕ} (hn : 0 < n) (r : Fin n → ℝ) (δ b : ℝ)
    (hmean : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = 0) :
    (n : ℝ)⁻¹ * ∑ i, (r i + b * Real.sqrt δ) ^ 2 = (b * Real.sqrt δ) ^ 2 := by
  have hr := mean_sq_zero hn r hmean
  simp_rw [hr, zero_add]
  exact mean_constant hn _

#print axioms mean_sq_zero
#print axioms mean_constant
#print axioms mean_sq_constant_cost
#print axioms mean_sq_zero_loss

#print axioms mse_nonneg
#print axioms mean_sq_scale
#print axioms mean_sq_loss_scale
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma worstCase_le_strict {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (p q : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ)
    (β : Fin d → ℝ) (γ : ℝ) (hγ : ‖WithLp.toLp p β‖ ^ 2 < γ) :
    worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
      (squareLoss β) ≤ ENNReal.ofReal
        (γ * δ + γ / (γ - ‖WithLp.toLp p β‖ ^ 2) * MSE X Y β) := by
  have hγpos : 0 < γ := lt_of_le_of_lt (sq_nonneg _) hγ
  have hcoef : 0 ≤ γ / (γ - ‖WithLp.toLp p β‖ ^ 2) :=
    div_nonneg hγpos.le (sub_pos.mpr hγ).le
  have hM := mse_nonneg X Y β
  calc
    _ ≤ ENNReal.ofReal γ * ENNReal.ofReal δ +
        ENNReal.ofReal (γ / (γ - ‖WithLp.toLp p β‖ ^ 2)) * ENNReal.ofReal (MSE X Y β) := by
      apply worstCase_upper_of_coupling_bound _ _ _ δ _ _
        (ne_of_gt (ENNReal.ofReal_pos.mpr hγpos)) ENNReal.ofReal_ne_top
      intro P _ π hπ
      have hi := coupling_integral_bound P (empiricalDistribution (fun i => (X i, Y i))) π
        hπ.2.1 hπ.2.2 (fun z => ENNReal.ofReal (squareLoss β z)) (squareLoss_measurable β)
        (fun z w => Nq q z w ^ 2) (ENNReal.ofReal γ)
        (ENNReal.ofReal (γ / (γ - ‖WithLp.toLp p β‖ ^ 2))) ENNReal.ofReal_ne_top
        (squareLoss_pointwise_upper p q hq hpq β γ hγ)
      rwa [empirical_squareLoss hn X Y β] at hi
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg hγpos.le hδ) (mul_nonneg hcoef hM),
        ENNReal.ofReal_mul hγpos.le, ENNReal.ofReal_mul hcoef]

#print axioms worstCase_le_strict
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma ennreal_le_of_glb (a : ENNReal) (s : Set ℝ) (v : ℝ) (hs : s.Nonempty)
    (hglb : IsGLB s v) (hpos : ∀ x ∈ s, 0 ≤ x)
    (hupper : ∀ x ∈ s, a ≤ ENNReal.ofReal x) : a ≤ ENNReal.ofReal v := by
  obtain ⟨x, hx⟩ := hs
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper x hx)
  have hbound : a.toReal ∈ lowerBounds s := by
    intro y hy
    exact (ENNReal.le_ofReal_iff_toReal_le ha (hpos y hy)).mp (hupper y hy)
  have hle : a.toReal ≤ v := hglb.2 hbound
  have hv : 0 ≤ v := (ENNReal.toReal_nonneg).trans hle
  exact (ENNReal.le_ofReal_iff_toReal_le ha hv).mpr hle

lemma worstCase_upper {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (p q : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ)
    (β : Fin d → ℝ) :
    worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
      (squareLoss β) ≤ ENNReal.ofReal
        ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let b := ‖WithLp.toLp p β‖
  let M := MSE X Y β
  let s : Set ℝ := {v | ∃ γ : ℝ, b ^ 2 < γ ∧ v = γ * δ + γ / (γ - b ^ 2) * M}
  have hM : 0 ≤ M := mse_nonneg X Y β
  have hb : 0 ≤ b := norm_nonneg _
  have hg : IsGLB s ((Real.sqrt M + b * Real.sqrt δ) ^ 2) :=
    RWPI.SqrtLasso.eq_29_minimization M b δ hM hb hδ
  have hs : s.Nonempty := ⟨(b ^ 2 + 1) * δ + (b ^ 2 + 1) / (b ^ 2 + 1 - b ^ 2) * M,
    ⟨b ^ 2 + 1, by linarith, rfl⟩⟩
  have hpos : ∀ x ∈ s, 0 ≤ x := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ0 : 0 ≤ γ := (sq_nonneg b).trans hγ.le
    exact add_nonneg (mul_nonneg hγ0 hδ)
      (mul_nonneg (div_nonneg hγ0 (sub_pos.mpr hγ).le) hM)
  have hupper : ∀ x ∈ s,
      worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
        (squareLoss β) ≤ ENNReal.ofReal x := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact worstCase_le_strict hn X Y p q hq hpq δ hδ β γ hγ
  have he := ennreal_le_of_glb _ s _ hs hg hpos hupper
  simpa only [b, M, mul_comm] using he

#print axioms ennreal_le_of_glb
#print axioms worstCase_upper
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open scoped BigOperators
open RWPI.SqrtLasso

lemma shift_cost {d : ℕ} (q : ENNReal) (hq : 1 ≤ q) (x v : Fin d → ℝ) (y t : ℝ)
    (hv : ‖WithLp.toLp q v‖ = 1) :
    Nq q (x - t • v, y) (x, y) ^ 2 = ENNReal.ofReal (t ^ 2) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have hs : x - t • v - x = -t • v := by ext j; simp
  simp only [Nq, ite_true]
  rw [hs]
  change (ENNReal.ofReal ‖(-t) • WithLp.toLp q v‖) ^ 2 = ENNReal.ofReal (t ^ 2)
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_neg,
    ← ENNReal.ofReal_pow (abs_nonneg t) 2, sq_abs]

lemma shift_squareLoss {d : ℕ} (β x v : Fin d → ℝ) (y t b : ℝ)
    (hv : ∑ j, β j * v j = b) :
    squareLoss β (x - t • v, y) = (y - ∑ j, β j * x j + b * t) ^ 2 := by
  unfold squareLoss
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hsum : ∑ j, β j * (t * v j) = t * b := by
    rw [← hv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

#print axioms shift_cost
#print axioms shift_squareLoss
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma ennreal_average_ofReal {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (n : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (a i) =
      ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, a i) := by
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ)⁻¹),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i)]

lemma shifted_empirical_cost {d n : ℕ} (hn : 0 < n) (q : ENNReal) (hq : 1 ≤ q)
    (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (v : Fin d → ℝ)
    (hv : ‖WithLp.toLp q v‖ = 1) (t : Fin n → ℝ) :
    transportCost (fun z w => Nq q z w ^ 2)
      (empiricalDistribution (fun i => (X i - t i • v, Y i)))
      (empiricalDistribution (fun i => (X i, Y i))) ≤
      ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, (t i) ^ 2) := by
  have hc := transportCost_le_empirical_cost hn
    (fun i => (X i - t i • v, Y i)) (fun i => (X i, Y i)) (fun z w => Nq q z w ^ 2)
  simp_rw [shift_cost q hq _ v _ _ hv] at hc
  rwa [ennreal_average_ofReal hn (fun i => (t i) ^ 2) (fun i => sq_nonneg _)] at hc

lemma worstCase_ge_shifted_mse {d n : ℕ} (hn : 0 < n) (q : ENNReal) (hq : 1 ≤ q)
    (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (β v : Fin d → ℝ)
    (hv : ‖WithLp.toLp q v‖ = 1) (t : Fin n → ℝ) (δ : ℝ)
    (ht : (n : ℝ)⁻¹ * ∑ i, (t i) ^ 2 ≤ δ) :
    ENNReal.ofReal (MSE (fun i => X i - t i • v) Y β) ≤
    worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
      (squareLoss β) := by
  have hc := (shifted_empirical_cost hn q hq X Y v hv t).trans (ENNReal.ofReal_le_ofReal ht)
  unfold worstCase
  apply le_iSup_of_le (empiricalDistribution (fun i => (X i - t i • v, Y i)))
  apply le_iSup_of_le (And.intro (empirical_probability hn _) hc)
  exact le_of_eq (empirical_squareLoss hn (fun i => X i - t i • v) Y β).symm

#print axioms ennreal_average_ofReal
#print axioms shifted_empirical_cost
#print axioms worstCase_ge_shifted_mse
end TransportCodex

set_option autoImplicit false
namespace TransportCodex
open MeasureTheory
open scoped BigOperators
open RWPI.SqrtLasso WassersteinDRO.Regularization

lemma worstCase_ge_empirical_mse {d n : ℕ} (hn : 0 < n) (q : ENNReal) (hq : 1 ≤ q)
    (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (β : Fin d → ℝ) (δ : ℝ) :
    ENNReal.ofReal (MSE X Y β) ≤
    worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
      (squareLoss β) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have hc := transportCost_le_empirical_cost hn (fun i => (X i, Y i))
    (fun i => (X i, Y i)) (fun z w => Nq q z w ^ 2)
  have hz : (n : ENNReal)⁻¹ * ∑ i, Nq q (X i, Y i) (X i, Y i) ^ 2 = 0 := by simp [Nq]
  rw [hz] at hc
  have hbudget := hc.trans (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal δ)
  unfold worstCase
  apply le_iSup_of_le (empiricalDistribution (fun i => (X i, Y i)))
  apply le_iSup_of_le (And.intro (empirical_probability hn _) hbudget)
  exact le_of_eq (empirical_squareLoss hn X Y β).symm

lemma worstCase_lower {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (p q : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ)
    (β : Fin d → ℝ) :
    ENNReal.ofReal ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2) ≤
    worstCase (fun z w => Nq q z w ^ 2) δ (empiricalDistribution (fun i => (X i, Y i)))
      (squareLoss β) := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let M := MSE X Y β
  let b := ‖WithLp.toLp p β‖
  let r : Fin n → ℝ := fun i => Y i - ∑ j, β j * X i j
  have hM : 0 ≤ M := mse_nonneg X Y β
  have hmean : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = M := rfl
  by_cases hβ : β = 0
  · have he := worstCase_ge_empirical_mse hn q hq.le X Y β δ
    simpa [hβ, Real.sq_sqrt (mse_nonneg X Y 0)] using he
  · have hb : 0 < b := lt_of_le_of_ne (norm_nonneg _)
      (by intro h; exact hβ ((norm_zero_iff p q hpq β).mp h.symm))
    obtain ⟨v, hv, hdot⟩ := norming_unit_of_positive p q hq hpq β hb
    by_cases hMpos : 0 < M
    · let t : Fin n → ℝ := fun i => Real.sqrt δ * r i / Real.sqrt M
      have ht : (n : ℝ)⁻¹ * ∑ i, (t i) ^ 2 = δ := mean_sq_scale r M δ hMpos hδ hmean
      have hloss : MSE (fun i => X i - t i • v) Y β = (Real.sqrt M + b * Real.sqrt δ) ^ 2 := by
        unfold MSE
        simp_rw [shift_squareLoss β _ v _ _ b hdot]
        exact mean_sq_loss_scale r M δ b hMpos hmean
      have he := worstCase_ge_shifted_mse hn q hq.le X Y β v hv t δ ht.le
      rw [hloss] at he
      simpa only [M, b, mul_comm] using he
    · have hMzero : M = 0 := le_antisymm (le_of_not_gt hMpos) hM
      let t : Fin n → ℝ := fun _ => Real.sqrt δ
      have ht : (n : ℝ)⁻¹ * ∑ i, (t i) ^ 2 = δ := mean_sq_constant_cost hn δ hδ
      have hz : (n : ℝ)⁻¹ * ∑ i, (r i) ^ 2 = 0 := hmean.trans hMzero
      have hloss : MSE (fun i => X i - t i • v) Y β = (b * Real.sqrt δ) ^ 2 := by
        unfold MSE
        simp_rw [shift_squareLoss β _ v _ _ b hdot]
        exact mean_sq_zero_loss hn r δ b hz
      have he := worstCase_ge_shifted_mse hn q hq.le X Y β v hv t δ ht.le
      rw [hloss] at he
      change ENNReal.ofReal ((Real.sqrt M + Real.sqrt δ * b) ^ 2) ≤ _
      rw [hMzero, Real.sqrt_zero, zero_add, mul_comm]
      exact he

#print axioms worstCase_ge_empirical_mse
#print axioms worstCase_lower
end TransportCodex

set_option autoImplicit false
open MeasureTheory RWPI.SqrtLasso
open scoped BigOperators

theorem solution {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (q p : ENNReal) (hq : 1 < q) (hpq : p.HolderConjugate q) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ β : Fin d → ℝ,
      worstCase (fun z w => Nq q z w ^ 2) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β) =
        ENNReal.ofReal ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2)) ∧
    (⨅ β : Fin d → ℝ, worstCase (fun z w => Nq q z w ^ 2) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β)) =
      ⨅ β : Fin d → ℝ, ENNReal.ofReal
          ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2) := by
  have hpoint (β : Fin d → ℝ) :
      worstCase (fun z w => Nq q z w ^ 2) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i : Fin n => (X i, Y i)))
          (squareLoss β) =
        ENNReal.ofReal ((Real.sqrt (MSE X Y β) + Real.sqrt δ * ‖WithLp.toLp p β‖) ^ 2) :=
    le_antisymm (TransportCodex.worstCase_upper hn X Y p q hq hpq δ hδ β)
      (TransportCodex.worstCase_lower hn X Y p q hq hpq δ hδ β)
  exact ⟨hpoint, iInf_congr hpoint⟩

#print axioms solution
