-- Prove2me | solution 1 for UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/aa47f784-317a-5395-8af9-584cbb1bf820

import Mathlib
import Theorems.Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue
import Theorems.Thm_Complex_locallyIntegrableOn_of_simplePoles
import Theorems.Thm_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero

open UpperHalfPlane Filter Complex MulAction MeasureTheory Set
open scoped MatrixGroups Topology ModularForm Real

noncomputable section

namespace LevelOneResidue

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem num_mul_denom_sub (γ : SL(2, ℤ)) (z w : ℂ) :
    num γ z * denom γ w - num γ w * denom γ z = z - w := by
  have h' := det_entries γ
  simp only [num, denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, Complex.ofReal_intCast]
  linear_combination (z - w) * h'

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem mob_sub_mob (γ : SL(2, ℤ)) {z w : ℂ} (hz : denom γ z ≠ 0) (hw : denom γ w ≠ 0) :
    mob γ z - mob γ w = (z - w) / (denom γ z * denom γ w) := by
  rw [mob, mob, div_sub_div _ _ hz hw, mul_comm (denom _ z) (num _ w), num_mul_denom_sub]

theorem analyticAt_denom (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (denom (γ : GL (Fin 2) ℝ)) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_num (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (num (γ : GL (Fin 2) ℝ)) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (mob γ) z :=
  (analyticAt_num γ z).div (analyticAt_denom γ z) (denom_ne_zero' γ hz)

theorem eventually_im_pos (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
  mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem tendsto_mob (σ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (mob σ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (mob σ τ)) := by
  refine tendsto_nhdsWithin_iff.2
    ⟨((analyticAt_mob σ τ.im_pos).continuousAt.tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [eventually_im_pos τ, self_mem_nhdsWithin] with z him hne
  rw [mem_compl_iff, mem_singleton_iff, ← sub_eq_zero,
    mob_sub_mob σ (denom_ne_zero' σ him) (denom_ne_zero' σ τ.im_pos)]
  exact div_ne_zero (sub_ne_zero.2 hne)
    (mul_ne_zero (denom_ne_zero' σ him) (denom_ne_zero' σ τ.im_pos))

theorem loc_slash (ω : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) {a : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g ((σ • τ : ℍ) : ℂ))
    (hω : ∀ᶠ w in 𝓝[≠] ((σ • τ : ℍ) : ℂ), ω (ofComplex w) = a / (w - (σ • τ : ℍ)) + g w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G τ ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), (ω ∣[(2 : ℤ)] σ) (ofComplex z) = a / (z - τ) + G z := by
  rw [coe_smul] at hg hω
  refine ⟨fun z => g (mob σ z) * (denom σ z ^ 2)⁻¹ - a * ((σ 1 0 : ℤ) : ℂ) / denom σ z,
    ?_, ?_⟩
  · exact ((hg.comp (analyticAt_mob σ τ.im_pos)).mul
      (((analyticAt_denom σ τ).pow 2).inv (pow_ne_zero _ (denom_ne_zero' σ τ.im_pos)))).sub
      ((analyticAt_const.mul analyticAt_const).div (analyticAt_denom σ τ)
        (denom_ne_zero' σ τ.im_pos))
  · have h1 := (tendsto_mob σ τ).eventually hω
    filter_upwards [h1, eventually_im_pos τ, self_mem_nhdsWithin] with z hz him hne
    have hoc : ofComplex z = ⟨z, him⟩ := ofComplex_apply_of_im_pos him
    have hsmul : σ • (⟨z, him⟩ : ℍ) = ofComplex (mob σ z) := by
      rw [← ofComplex_apply (σ • ⟨z, him⟩), coe_smul]
    rw [ModularForm.SL_slash_apply, hoc, hsmul, hz]
    have hcoe : ((⟨z, him⟩ : ℍ) : ℂ) = z := rfl
    rw [hcoe, mob_sub_mob σ (denom_ne_zero' σ him) (denom_ne_zero' σ τ.im_pos)]
    have hzτ : z - τ ≠ 0 := sub_ne_zero.2 hne
    have hDz := denom_ne_zero' σ him
    have hDτ := denom_ne_zero' σ τ.im_pos
    have hrel : denom σ τ = denom σ z - ((σ 1 0 : ℤ) : ℂ) * (z - τ) := by
      simp only [denom_eq]; ring
    rw [hrel] at hDτ ⊢
    generalize denom σ z = Dz at hDz hDτ ⊢
    rw [zpow_neg, zpow_ofNat]
    field_simp
    ring

theorem residue_unique {F : ℂ → ℂ} {z₀ : ℂ} {a b : ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hg' : AnalyticAt ℂ g' z₀)
    (h : ∀ᶠ z in 𝓝[≠] z₀, F z = a / (z - z₀) + g z)
    (h' : ∀ᶠ z in 𝓝[≠] z₀, F z = b / (z - z₀) + g' z) : a = b := by
  have hev : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * (g' z - g z) = a - b := by
    filter_upwards [h, h', self_mem_nhdsWithin] with z hz hz' hne
    have hzne : z - z₀ ≠ 0 := sub_ne_zero.2 hne
    have e := hz.symm.trans hz'
    rw [div_add' _ _ _ hzne, div_add' _ _ _ hzne, div_left_inj' hzne] at e
    linear_combination -e
  have hlim : Tendsto (fun z => (z - z₀) * (g' z - g z)) (𝓝[≠] z₀) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - z₀) * (g' z - g z)) z₀ :=
      (continuousAt_id.sub continuousAt_const).mul (hg'.continuousAt.sub hg.continuousAt)
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℂ => a - b) (𝓝[≠] z₀) (𝓝 (a - b)) := tendsto_const_nhds
  have := tendsto_nhds_unique (hlim.congr' hev) hconst
  exact (sub_eq_zero.1 this.symm)

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

theorem finite_stabilizer (x : ℍ) : (stabilizer SL(2, ℤ) x : Set SL(2, ℤ)).Finite := by
  refine (finite_moving {x} {x} isCompact_singleton isCompact_singleton).subset ?_
  intro γ hγ
  simp only [SetLike.mem_coe, mem_stabilizer_iff] at hγ
  exact ⟨x, ⟨x, mem_singleton _, hγ⟩, mem_singleton _⟩

scoped instance (x : ℍ) : Finite (stabilizer SL(2, ℤ) x) := (finite_stabilizer x).to_subtype

theorem im_smul_le_inv (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) ≠ 0) :
    (γ • τ).im ≤ τ.im⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have h1 := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g := (γ : GL (Fin 2) ℝ)) (z := τ)
  have hc' : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
      have := Int.one_le_abs hc
      nlinarith [sq_abs (γ 1 0)]
    exact_mod_cast this
  have hτ := τ.im_pos
  have hent : ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = ((γ 1 0 : ℤ) : ℝ) := by simp
  rw [hent] at h1
  have hns : τ.im ^ 2 ≤ Complex.normSq (denom γ τ) := by
    calc τ.im ^ 2 = 1 * τ.im ^ 2 := by ring
      _ ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * τ.im ^ 2 := by gcongr
      _ = (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by ring
      _ ≤ _ := h1
  have hpos : 0 < Complex.normSq (denom γ τ) := lt_of_lt_of_le (by positivity) hns
  rw [div_le_iff₀ hpos]
  calc τ.im = τ.im⁻¹ * τ.im ^ 2 := by field_simp
    _ ≤ τ.im⁻¹ * Complex.normSq (denom γ τ) := by gcongr

theorem denom_of_c_eq_zero (γ : SL(2, ℤ)) (z : ℂ) (hc : (γ 1 0 : ℤ) = 0) :
    denom γ z = ((γ 1 1 : ℤ) : ℂ) := by
  rw [denom_eq, hc]; simp

theorem d_sq_of_c_eq_zero (γ : SL(2, ℤ)) (hc : (γ 1 0 : ℤ) = 0) :
    (γ 0 0 : ℤ) * γ 1 1 = 1 ∧ (γ 1 1 : ℤ) * γ 1 1 = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
  refine ⟨h, ?_⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> norm_num

theorem im_smul_of_c_eq_zero (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) = 0) :
    (γ • τ).im = τ.im := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_of_c_eq_zero γ _ hc]
  have h2 := (d_sq_of_c_eq_zero γ hc).2
  have : Complex.normSq (((γ 1 1 : ℤ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_intCast, Complex.normSq_ofReal]; exact_mod_cast h2
  rw [this, div_one]

theorem coe_smul_of_c_eq_zero (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) = 0) :
    ((γ • τ : ℍ) : ℂ) = (τ : ℂ) + (((γ 0 1 : ℤ) * γ 1 1 : ℤ) : ℂ) := by
  obtain ⟨had, hdd⟩ := d_sq_of_c_eq_zero γ hc
  rw [coe_smul, mob, num_eq, denom_of_c_eq_zero γ _ hc]
  have had' : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) = 1 := by exact_mod_cast had
  have hdd' : ((γ 1 1 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) = 1 := by exact_mod_cast hdd
  have hd : ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdd'; exact zero_ne_one hdd'
  rw [div_eq_iff hd]
  push_cast
  linear_combination (-(τ : ℂ) * ((γ 0 0 : ℤ) : ℂ) - ((γ 0 1 : ℤ) : ℂ)) * hdd'
    + (τ : ℂ) * ((γ 1 1 : ℤ) : ℂ) * had'

theorem im_smul_le_max (γ : SL(2, ℤ)) (τ : ℍ) : (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  by_cases hc : (γ 1 0 : ℤ) = 0
  · rw [im_smul_of_c_eq_zero γ τ hc]; exact le_max_left _ _
  · exact (im_smul_le_inv γ τ hc).trans (le_max_right _ _)

theorem exists_smul_nice (τ : ℍ) : ∃ γ : SL(2, ℤ),
    |(γ • τ).re| ≤ 1 / 2 ∧ 3 / 4 ≤ (γ • τ).im ∧ (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨γ, hγ.2, ?_, im_smul_le_max γ τ⟩
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  nlinarith [(γ • τ).im_pos]

section Invariance

variable {ω : ℍ → ℂ} (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
include hΓ

theorem apply_smul (γ : SL(2, ℤ)) (τ : ℍ) : ω (γ • τ) = ω τ * denom γ τ ^ 2 := by
  have h := congrFun (hΓ γ) τ
  rw [ModularForm.SL_slash_apply] at h
  rw [← h, mul_assoc, ← zpow_natCast, ← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ _)]
  simp

theorem apply_vadd_one (τ : ℍ) : ω ((1 : ℝ) +ᵥ τ) = ω τ := by
  rw [← modular_T_smul, apply_smul hΓ]
  simp [ModularGroup.denom_apply, ModularGroup.T]

theorem apply_vadd_int (n : ℤ) (τ : ℍ) : ω ((n : ℝ) +ᵥ τ) = ω τ := by
  rw [← modular_T_zpow_smul]
  set γ : SL(2, ℤ) := ModularGroup.T ^ n with hγdef
  rw [apply_smul hΓ]
  have h1 : denom γ τ = 1 := by
    rw [ModularGroup.denom_apply]
    have h10 : γ 1 0 = 0 := by
      change (ModularGroup.T ^ n).1 1 0 = 0
      rw [ModularGroup.coe_T_zpow]; simp
    have h11 : γ 1 1 = 1 := by
      change (ModularGroup.T ^ n).1 1 1 = 1
      rw [ModularGroup.coe_T_zpow]; simp
    rw [h10, h11]; simp
  rw [h1]; simp

theorem residue_smul {c : ℍ → ℂ}
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (γ : SL(2, ℤ)) (τ : ℍ) : c (γ • τ) = c τ := by
  obtain ⟨g, hg, hω⟩ := hloc (γ • τ)
  obtain ⟨G, hG, hω'⟩ := loc_slash ω γ τ hg hω
  rw [hΓ γ] at hω'
  obtain ⟨g', hg', hω''⟩ := hloc τ
  exact residue_unique hG hg' hω' hω''

end Invariance

section Cutoff

local notation "st" => Real.smoothTransition

theorem st_half : st (1 / 2 : ℝ) = 1 / 2 := by
  unfold Real.smoothTransition
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h]
  have hp := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [div_eq_iff (by positivity)]
  ring

theorem deriv_st_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : deriv st x = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun y => by
    rw [Real.smoothTransition.zero_of_nonpos hx]; exact Real.smoothTransition.nonneg y)

theorem deriv_st_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : deriv st x = 0 :=
  IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall fun y => by
    rw [Real.smoothTransition.one_of_one_le hx]; exact Real.smoothTransition.le_one y)

theorem mem_Ioo_of_deriv_st_ne_zero {x : ℝ} (h : deriv st x ≠ 0) : 0 < x ∧ x < 1 := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h' <;> push Not at h'
  exacts [h (deriv_st_eq_zero_of_nonpos h'), h (deriv_st_eq_zero_of_one_le h')]

theorem st_differentiable : Differentiable ℝ st :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero

theorem continuous_deriv_st : Continuous (deriv st) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

def pOne (x : ℝ) : ℝ := st (x + 1) - st x

theorem pOne_contDiff : ContDiff ℝ 1 pOne :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem pOne_nonneg (x : ℝ) : 0 ≤ pOne x :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

theorem pOne_le_one (x : ℝ) : pOne x ≤ 1 := by
  have := Real.smoothTransition.le_one (x + 1)
  have := Real.smoothTransition.nonneg x
  unfold pOne; linarith

theorem pOne_eq_zero_of_le {x : ℝ} (hx : x ≤ -1) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith),
    Real.smoothTransition.zero_of_nonpos (show x ≤ 0 by linarith)]

theorem pOne_eq_zero_of_ge {x : ℝ} (hx : 1 ≤ x) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith),
    Real.smoothTransition.one_of_one_le hx]

theorem mem_Ioo_of_pOne_ne_zero {x : ℝ} (hx : pOne x ≠ 0) : -1 < x ∧ x < 1 := by
  by_contra h
  rcases not_and_or.1 h with h | h <;> push Not at h
  exacts [hx (pOne_eq_zero_of_le h), hx (pOne_eq_zero_of_ge h)]

theorem half_le_pOne {x : ℝ} (hx : |x| ≤ 1 / 2) : 1 / 2 ≤ pOne x := by
  rcases abs_le.1 hx with ⟨h1, h2⟩
  unfold pOne
  rcases le_total x 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, ← st_half]
    exact Real.smoothTransition.monotone (by linarith)
  · rw [Real.smoothTransition.one_of_one_le (by linarith)]
    have := Real.smoothTransition.monotone (show x ≤ 1 / 2 by linarith)
    rw [st_half] at this
    linarith

theorem pOne_sub_one_add {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : pOne (u - 1) + pOne u = 1 := by
  unfold pOne
  rw [sub_add_cancel, Real.smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ u + 1)]
  ring

theorem eq_floor_of_pOne_ne_zero (x : ℝ) (n : ℤ) (hn : pOne (x + n) ≠ 0) :
    n = ⌊-x⌋ ∨ n = ⌊-x⌋ + 1 := by
  obtain ⟨h1, h2⟩ := mem_Ioo_of_pOne_ne_zero hn
  have h3 := Int.floor_le (-x)
  have h4 := Int.lt_floor_add_one (-x)
  have h5 : ((⌊-x⌋ - 1 : ℤ) : ℝ) < n := by push_cast; linarith
  have h6 : (n : ℝ) < ((⌊-x⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
  have h5' := Int.cast_lt.1 h5
  have h6' := Int.cast_lt.1 h6
  omega

theorem pOne_floor_add (x : ℝ) : pOne (x + ⌊-x⌋) + pOne (x + ((⌊-x⌋ + 1 : ℤ) : ℝ)) = 1 := by
  have h3 := Int.floor_le (-x)
  have h4 := Int.lt_floor_add_one (-x)
  have := pOne_sub_one_add (u := x + ((⌊-x⌋ + 1 : ℤ) : ℝ)) (by push_cast; linarith)
    (by push_cast; linarith)
  convert this using 2
  push_cast; ring_nf

theorem finsum_pOne (x : ℝ) : ∑ᶠ n : ℤ, pOne (x + n) = 1 := by
  rw [finsum_eq_sum_of_support_subset (s := {⌊-x⌋, ⌊-x⌋ + 1})]
  · rw [Finset.sum_pair (by omega)]
    exact_mod_cast pOne_floor_add x
  · intro n hn
    rcases eq_floor_of_pOne_ne_zero x n hn with h | h <;> simp [h]

def pTwo (T y : ℝ) : ℝ := st (8 * y - 5) * st (T + 4 - y)

theorem pTwo_contDiff (T : ℝ) : ContDiff ℝ 1 (pTwo T) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem pTwo_nonneg (T y : ℝ) : 0 ≤ pTwo T y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem pTwo_le_one (T y : ℝ) : pTwo T y ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem pTwo_eq_zero_of_le {T y : ℝ} (hy : y ≤ 5 / 8) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show 8 * y - 5 ≤ 0 by linarith)]

theorem pTwo_eq_zero_of_ge {T y : ℝ} (hy : T + 4 ≤ y) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show T + 4 - y ≤ 0 by linarith)]

theorem pTwo_eq_one {T y : ℝ} (h1 : 3 / 4 ≤ y) (h2 : y ≤ T + 3) : pTwo T y = 1 := by
  simp [pTwo, Real.smoothTransition.one_of_one_le (show 1 ≤ 8 * y - 5 by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ T + 4 - y by linarith)]

theorem mem_Ioo_of_pTwo_ne_zero {T y : ℝ} (h : pTwo T y ≠ 0) : 5 / 8 < y ∧ y < T + 4 := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h' <;> push Not at h'
  exacts [h (pTwo_eq_zero_of_le h'), h (pTwo_eq_zero_of_ge h')]

def bump (T : ℝ) (z : ℂ) : ℝ := pOne z.re * pTwo T z.im

theorem bump_contDiff (T : ℝ) : ContDiff ℝ 1 (bump T) :=
  (pOne_contDiff.comp Complex.reCLM.contDiff).mul ((pTwo_contDiff T).comp Complex.imCLM.contDiff)

theorem bump_nonneg (T : ℝ) (z : ℂ) : 0 ≤ bump T z := mul_nonneg (pOne_nonneg _) (pTwo_nonneg _ _)

theorem bump_le_one (T : ℝ) (z : ℂ) : bump T z ≤ 1 :=
  mul_le_one₀ (pOne_le_one _) (pTwo_nonneg _ _) (pTwo_le_one _ _)

theorem mem_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) :
    (-1 < z.re ∧ z.re < 1) ∧ (5 / 8 < z.im ∧ z.im < T + 4) :=
  ⟨mem_Ioo_of_pOne_ne_zero (left_ne_zero_of_mul h),
    mem_Ioo_of_pTwo_ne_zero (right_ne_zero_of_mul h)⟩

theorem im_pos_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) : 0 < z.im := by
  have := (mem_of_bump_ne_zero h).2.1; linarith

theorem half_le_bump {T : ℝ} {z : ℂ} (h1 : |z.re| ≤ 1 / 2) (h2 : 3 / 4 ≤ z.im)
    (h3 : z.im ≤ T + 3) : 1 / 2 ≤ bump T z := by
  unfold bump; rw [pTwo_eq_one h2 h3, mul_one]; exact half_le_pOne h1

def box (T : ℝ) : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (5 / 8 : ℝ) (T + 4)

theorem isCompact_box (T : ℝ) : IsCompact (box T) := isCompact_Icc.reProdIm isCompact_Icc

theorem isClosed_box (T : ℝ) : IsClosed (box T) := isClosed_Icc.reProdIm isClosed_Icc

theorem im_pos_of_mem_box {T : ℝ} {z : ℂ} (hz : z ∈ box T) : 0 < z.im := by
  have := (mem_reProdIm.1 hz).2.1; linarith

theorem support_bump_subset (T : ℝ) : Function.support (bump T) ⊆ box T := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_of_bump_ne_zero hz
  exact mem_reProdIm.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

theorem tsupport_bump_subset (T : ℝ) : tsupport (bump T) ⊆ box T :=
  closure_minimal (support_bump_subset T) (isClosed_box T)

def boxH (T : ℝ) : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' box T

theorem isCompact_coe_preimage {K : Set ℂ} (hK : IsCompact K) (hK' : K ⊆ {z : ℂ | 0 < z.im}) :
    IsCompact (((↑) : ℍ → ℂ) ⁻¹' K) := by
  refine isEmbedding_coe.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset]
  · exact hK
  · intro z hz; exact ⟨⟨z, hK' hz⟩, rfl⟩

theorem isCompact_boxH (T : ℝ) : IsCompact (boxH T) :=
  isCompact_coe_preimage (isCompact_box T) fun _ hz => im_pos_of_mem_box hz

def recip (t : ℝ) : ℝ := st (4 * t - 1) / t

theorem recip_contDiff : ContDiff ℝ 1 recip := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases lt_or_ge (1 / 8 : ℝ) t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).div contDiffAt_id
      (by positivity)
  · have : recip =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
      simp [recip, Real.smoothTransition.zero_of_nonpos (by linarith [hs.out] : 4 * s - 1 ≤ 0)]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem mul_recip_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) : t * recip t = 1 := by
  unfold recip
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  field_simp

def gcut (T : ℝ) (z : ℂ) : ℝ := 1 - st (z.im - T)

theorem gcut_contDiff (T : ℝ) : ContDiff ℝ 1 (gcut T) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (Complex.imCLM.contDiff.sub
    contDiff_const))

theorem gcut_eq_one {T : ℝ} {z : ℂ} (h : z.im ≤ T) : gcut T z = 1 := by
  simp [gcut, Real.smoothTransition.zero_of_nonpos (show z.im - T ≤ 0 by linarith)]

theorem gcut_eq_zero {T : ℝ} {z : ℂ} (h : T + 1 ≤ z.im) : gcut T z = 0 := by
  simp [gcut, Real.smoothTransition.one_of_one_le (show 1 ≤ z.im - T by linarith)]

theorem hasFDerivAt_gcut (T : ℝ) (z : ℂ) :
    HasFDerivAt (gcut T) (-(deriv st (z.im - T) • Complex.imCLM)) z := by
  have h1 : HasFDerivAt (fun w : ℂ => w.im - T) Complex.imCLM z :=
    Complex.imCLM.hasFDerivAt.sub_const T
  have h2 : HasDerivAt st (deriv st (z.im - T)) (z.im - T) :=
    (st_differentiable _).hasDerivAt
  exact (h2.comp_hasFDerivAt z h1).const_sub 1

theorem fderiv_gcut_one (T : ℝ) (z : ℂ) : fderiv ℝ (gcut T) z 1 = 0 := by
  rw [(hasFDerivAt_gcut T z).fderiv]; simp

theorem fderiv_gcut_I (T : ℝ) (z : ℂ) : fderiv ℝ (gcut T) z Complex.I = -deriv st (z.im - T) := by
  rw [(hasFDerivAt_gcut T z).fderiv]; simp

end Cutoff

section Partition

local notation "st" => Real.smoothTransition

def cover (T : ℝ) (z : ℂ) : ℝ := ∑ᶠ γ : SL(2, ℤ), bump T (mob γ z)

theorem hasFiniteSupport_bump_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => bump T (mob γ τ) := by
  refine (finite_moving {τ} (boxH T) isCompact_singleton (isCompact_boxH T)).subset ?_
  intro γ hγ
  refine ⟨γ • τ, ⟨τ, rfl, rfl⟩, ?_⟩
  show ((γ • τ : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem cover_nonneg (T : ℝ) (z : ℂ) : 0 ≤ cover T z := finsum_nonneg fun _ => bump_nonneg _ _

theorem bump_le_cover (T : ℝ) (τ : ℍ) (γ : SL(2, ℤ)) : bump T (mob γ τ) ≤ cover T τ :=
  single_le_finsum γ (hasFiniteSupport_bump_mob T τ) fun _ => bump_nonneg _ _

theorem mob_mob (γ γ' : SL(2, ℤ)) (τ : ℍ) : mob γ (mob γ' τ) = mob (γ * γ') τ := by
  rw [← coe_smul, ← coe_smul, ← coe_smul, mul_smul]

theorem cover_mob (T : ℝ) (γ' : SL(2, ℤ)) (τ : ℍ) : cover T (mob γ' τ) = cover T τ := by
  unfold cover
  simp_rw [mob_mob]
  exact finsum_comp_equiv (Equiv.mulRight γ') (f := fun γ => bump T (mob γ τ))

theorem half_le_cover {T : ℝ} (τ : ℍ) (h1 : τ.im ≤ T + 3) (h2 : τ.im⁻¹ ≤ T + 3) :
    1 / 2 ≤ cover T τ := by
  obtain ⟨γ, hre, him, him'⟩ := exists_smul_nice τ
  refine le_trans ?_ (bump_le_cover T τ γ)
  rw [← coe_smul]
  apply half_le_bump
  · rw [coe_re]; exact hre
  · rw [coe_im]; exact him
  · rw [coe_im]; exact him'.trans (max_le h1 h2)

def pu (T : ℝ) (z : ℂ) : ℝ := bump T z * recip (cover T z)

theorem finsum_pu_mob {T : ℝ} (τ : ℍ) (h : 1 / 2 ≤ cover T τ) :
    ∑ᶠ γ : SL(2, ℤ), pu T (mob γ τ) = 1 := by
  unfold pu
  simp_rw [cover_mob]
  rw [← finsum_mul]
  exact mul_recip_of_half_le h

theorem support_pu_subset (T : ℝ) : Function.support (pu T) ⊆ Function.support (bump T) :=
  fun _ hz => left_ne_zero_of_mul hz

theorem tsupport_pu_subset (T : ℝ) : tsupport (pu T) ⊆ box T :=
  (closure_mono (support_pu_subset T)).trans (tsupport_bump_subset T)

theorem hasFiniteSupport_pu_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => pu T (mob γ τ) :=
  (hasFiniteSupport_bump_mob T τ).subset fun _ hγ => support_pu_subset T hγ

theorem cover_eventuallyEq_sum (T : ℝ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    ∃ s : Finset SL(2, ℤ), cover T =ᶠ[𝓝 z₀] fun z => ∑ γ ∈ s, bump T (mob γ z) := by
  have hN : Metric.closedBall z₀ (z₀.im / 2) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 := abs_im_le_norm (z - z₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [sub_im] at h1
    have := (abs_le.1 (h1.trans hz)).1
    show 0 < z.im
    linarith
  have hNH : IsCompact (((↑) : ℍ → ℂ) ⁻¹' Metric.closedBall z₀ (z₀.im / 2)) :=
    isCompact_coe_preimage (isCompact_closedBall _ _) hN
  have hfin := finite_moving _ (boxH T) hNH (isCompact_boxH T)
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds z₀ (by positivity : 0 < z₀.im / 2)] with z hz
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  simp only [Set.Finite.coe_toFinset, mem_setOf_eq]
  refine ⟨γ • ⟨z, hN hz⟩, ⟨⟨z, hN hz⟩, hz, rfl⟩, ?_⟩
  show ((γ • (⟨z, hN hz⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem mob_contDiffAt (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ 1 (mob γ) z :=
  ((analyticAt_mob γ hz).contDiffAt).restrict_scalars ℝ

theorem cover_contDiffAt (T : ℝ) {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ 1 (cover T) z := by
  obtain ⟨s, hs⟩ := cover_eventuallyEq_sum T hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hs
  exact ContDiffAt.sum fun γ _ => (bump_contDiff T).contDiffAt.comp z (mob_contDiffAt γ hz)

theorem pu_contDiff (T : ℝ) : ContDiff ℝ 1 (pu T) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge 0 z.im with hz | hz
  · exact (bump_contDiff T).contDiffAt.mul (recip_contDiff.contDiffAt.comp z
      (cover_contDiffAt T hz))
  · have : pu T =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Iio).mem_nhds
        (show z ∈ Complex.im ⁻¹' Iio (5 / 8 : ℝ) by simp; linarith)] with w hw
      have hb : bump T w = 0 := by
        by_contra hb
        have := (mem_of_bump_ne_zero hb).2.1
        simp at hw; linarith
      simp [pu, hb]
    exact contDiffAt_const.congr_of_eventuallyEq this

end Partition

section Poles

theorem eventually_residue_zero {ω c : ℍ → ℂ}
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), c (ofComplex z) = 0 := by
  obtain ⟨g, hg, hω⟩ := hloc τ
  have h1 : ∀ᶠ z : ℂ in 𝓝 (τ : ℂ), z ≠ (τ : ℂ) → ω (ofComplex z) = c τ / (z - τ) + g z :=
    eventually_nhdsWithin_iff.1 hω
  have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im := isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
  have h3 := (h1.and (hg.eventually_analyticAt.and h2)).eventually_nhds
  refine eventually_nhdsWithin_iff.2 (h3.mono fun z hz hne => ?_)
  have hzτ : z ≠ (τ : ℂ) := hne
  obtain ⟨-, hgz, hzim⟩ := hz.self_of_nhds
  have hG : AnalyticAt ℂ (fun w => c τ / (w - τ) + g w) z :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hzτ)).add hgz
  have hexp : ∀ᶠ w in 𝓝[≠] z, ω (ofComplex w) = 0 / (w - z) + (c τ / (w - τ) + g w) := by
    have hne' : ∀ᶠ w in 𝓝 z, w ≠ (τ : ℂ) := isOpen_ne.mem_nhds hzτ
    refine mem_nhdsWithin_of_mem_nhds ((hz.and hne').mono fun w hw => ?_)
    rw [zero_div, zero_add]
    exact hw.1.1 hw.2
  obtain ⟨g₂, hg₂, hω₂⟩ := hloc (ofComplex z)
  rw [ofComplex_apply_of_im_pos hzim] at hg₂ hω₂ ⊢
  exact residue_unique hg₂ hG hω₂ hexp

theorem finite_poles {ω c : ℍ → ℂ}
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ {z : ℂ | 0 < z.im}) :
    {a ∈ K | c (ofComplex a) ≠ 0}.Finite := by
  let V : ℂ → Set ℂ := fun a => {w | w ≠ a → c (ofComplex w) = 0}
  have hV : ∀ a ∈ K, V a ∈ 𝓝 a := fun a ha =>
    eventually_nhdsWithin_iff.1 (eventually_residue_zero hloc ⟨a, hKU ha⟩)
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover V hV
  refine t.finite_toSet.subset fun a ⟨haK, hca⟩ => ?_
  obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (ht haK)
  by_contra hat
  exact hca (hax fun h => hat (h ▸ hx))

theorem finsum_mob_eq_card_mul_sum (x : ℍ) (f : ℂ → ℝ) (O : Finset ℂ)
    (hO : ∀ a ∈ O, ∃ γ : SL(2, ℤ), mob γ x = a)
    (hA : ∀ γ : SL(2, ℤ), f (mob γ x) ≠ 0 → mob γ x ∈ O) :
    ∑ᶠ γ : SL(2, ℤ), f (mob γ x) = Nat.card (stabilizer SL(2, ℤ) x) * ∑ a ∈ O, f a := by
  classical
  choose! g hg using hO
  set St := (finite_stabilizer x).toFinset with hSt
  have hmem : ∀ s, s ∈ St ↔ s • x = x := fun s => by
    rw [hSt, Set.Finite.mem_toFinset]; exact mem_stabilizer_iff
  have hstab : ∀ s ∈ St, mob s x = x := fun s hs => by
    rw [← coe_smul, (hmem s).1 hs]
  let Ψ : ℂ × SL(2, ℤ) → SL(2, ℤ) := fun p => g p.1 * p.2
  have hinj : Set.InjOn Ψ ↑(O ×ˢ St) := by
    rintro ⟨a, s⟩ hp ⟨b, s'⟩ hq he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
    have hab : a = b := by
      rw [← hg a hp.1, ← hg b hq.1]
      have e1 : mob (g a) x = mob (g a * s) x := by rw [← mob_mob, hstab s hp.2]
      have e2 : mob (g b) x = mob (g b * s') x := by rw [← mob_mob, hstab s' hq.2]
      rw [e1, e2]
      exact congrArg (fun γ => mob γ x) he
    subst hab
    have hss : s = s' := mul_left_cancel he
    rw [hss]
  have hcard : (Nat.card (stabilizer SL(2, ℤ) x) : ℝ) = St.card := by
    rw [hSt, ← Set.ncard_eq_toFinset_card _ (finite_stabilizer x), ← Nat.card_coe_set_eq]
    rfl
  rw [finsum_eq_sum_of_support_subset (s := (O ×ˢ St).image Ψ)]
  · rw [Finset.sum_image hinj, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : ∀ s ∈ St, f (mob (Ψ (a, s)) x) = f a := fun s hs => by
      simp only [Ψ]
      rw [← mob_mob, hstab s hs, hg a ha]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
  · intro γ hγ
    have haO : mob γ x ∈ O := hA γ hγ
    rw [Finset.coe_image]
    refine ⟨(mob γ x, (g (mob γ x))⁻¹ * γ), ?_, ?_⟩
    · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      refine ⟨haO, (hmem _).2 ?_⟩
      rw [mul_smul, inv_smul_eq_iff]
      ext1
      rw [coe_smul, coe_smul, hg _ haO]
    · simp [Ψ]

theorem finsum_residue_mul_eq {c : ℍ → ℂ} {S : Finset ℍ} {T : ℝ} {hr : ℂ → ℝ}
    (hfin : {a ∈ box T | c (ofComplex a) ≠ 0}.Finite)
    (hcs : ∀ (γ : SL(2, ℤ)) (τ : ℍ), c (γ • τ) = c τ)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ')
    (h1 : Function.support hr ⊆ box T)
    (h2 : ∀ σ ∈ S, c σ ≠ 0 → ∑ᶠ γ : SL(2, ℤ), hr (mob γ σ) = 1) :
    ∑ᶠ a : ℂ, c (ofComplex a) * (hr a : ℂ) =
      ∑ σ ∈ S, c σ / Nat.card (stabilizer SL(2, ℤ) σ) := by
  classical
  set A := hfin.toFinset with hA
  have hmemA : ∀ a, a ∈ A ↔ a ∈ box T ∧ c (ofComplex a) ≠ 0 := fun a => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  have hrep : ∀ a ∈ A, ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = ofComplex a := fun a ha =>
    hS _ ((hmemA a).1 ha).2
  choose! r hrS γr hγr using hrep
  have hsupp : Function.support (fun a : ℂ => c (ofComplex a) * (hr a : ℂ)) ⊆ ↑A := by
    intro a ha
    rw [Function.mem_support] at ha
    have hr0 : hr a ≠ 0 := fun h => ha (by simp [h])
    have hc0 : c (ofComplex a) ≠ 0 := fun h => ha (by simp [h])
    exact (hmemA a).2 ⟨h1 hr0, hc0⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [← Finset.sum_fiberwise_of_maps_to (g := r) (fun a ha => hrS a ha)]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hfib : ∀ a ∈ A.filter (fun a => r a = σ), c (ofComplex a) = c σ := fun a ha => by
    obtain ⟨haA, hra⟩ := Finset.mem_filter.1 ha
    rw [← hγr a haA, hcs, hra]
  rw [Finset.sum_congr rfl (fun a ha => by rw [hfib a ha]), ← Finset.mul_sum]
  by_cases hcσ : c σ = 0
  · simp [hcσ]
  have hfilter : A.filter (fun a => r a = σ) =
      A.filter (fun a => ∃ γ : SL(2, ℤ), mob γ σ = a) := by
    refine Finset.filter_congr fun a haA => ⟨fun hra => ?_, fun ⟨γ, hγ⟩ => ?_⟩
    · have hh := hγr a haA
      rw [hra] at hh
      refine ⟨γr a, ?_⟩
      rw [← coe_smul, hh, ofComplex_apply_of_im_pos (im_pos_of_mem_box ((hmemA a).1 haA).1)]
    · have hoa : ofComplex a = γ • σ := by rw [← hγ, ← coe_smul, ofComplex_apply]
      have hh := hγr a haA
      rw [hoa] at hh
      have : (γ⁻¹ * γr a) • r a = σ := by rw [mul_smul, hh, inv_smul_smul]
      exact hinj _ (hrS a haA) _ hσ _ this
  rw [hfilter]
  have horb := finsum_mob_eq_card_mul_sum σ hr (A.filter fun a => ∃ γ : SL(2, ℤ), mob γ σ = a)
    (fun a ha => (Finset.mem_filter.1 ha).2)
    (fun γ hγ => Finset.mem_filter.2 ⟨(hmemA _).2 ⟨h1 hγ, by
      rwa [← coe_smul, ofComplex_apply, hcs]⟩, γ, rfl⟩)
  rw [h2 σ hσ hcσ] at horb
  have hpos : (0 : ℝ) < Nat.card (stabilizer SL(2, ℤ) σ) := by
    have : 0 < Nat.card (stabilizer SL(2, ℤ) σ) := Nat.card_pos
    exact_mod_cast this
  have hsum : ∑ a ∈ A with ∃ γ : SL(2, ℤ), mob γ σ = a, hr a =
      ((Nat.card (stabilizer SL(2, ℤ) σ) : ℝ))⁻¹ := by
    field_simp
    linarith [horb]
  have hsumC : ∑ a ∈ A with ∃ γ : SL(2, ℤ), mob γ σ = a, (hr a : ℂ) =
      ((Nat.card (stabilizer SL(2, ℤ) σ) : ℂ))⁻¹ := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hsum
    push_cast at this
    exact this
  rw [hsumC, div_eq_mul_inv]

end Poles

section Calculus

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

def dbarR (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  ((fderiv ℝ u z 1 : ℝ) + Complex.I * (fderiv ℝ u z Complex.I : ℝ)) / 2

theorem dbar_ofReal {u : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    (fderiv ℝ (fun w => (u w : ℂ)) z 1 +
        Complex.I * fderiv ℝ (fun w => (u w : ℂ)) z Complex.I) / 2 = dbarR u z := by
  have h : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hu.hasFDerivAt
  rw [h.fderiv]
  simp [dbarR]

theorem dbarR_of_notMem_tsupport {u : ℂ → ℝ} {z : ℂ} (h : z ∉ tsupport u) : dbarR u z = 0 := by
  simp [dbarR, fderiv_of_notMem_tsupport ℝ h]

theorem dbarR_congr {u v : ℂ → ℝ} {z : ℂ} (h : u =ᶠ[𝓝 z] v) : dbarR u z = dbarR v z := by
  simp only [dbarR, h.fderiv_eq]

theorem dbarR_mul {u v : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    dbarR (fun w => u w * v w) z = u z * dbarR v z + v z * dbarR u z := by
  simp only [dbarR, fderiv_fun_mul hu hv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dbarR_sum {ι : Type*} (s : Finset ι) (u : ι → ℂ → ℝ) (z : ℂ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (u i) z) :
    dbarR (fun w => ∑ i ∈ s, u i w) z = ∑ i ∈ s, dbarR (u i) z := by
  simp only [dbarR, fderiv_fun_sum h, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

theorem dbarR_comp {u : ℂ → ℝ} {m : ℂ → ℂ} {m' z : ℂ} (hm : HasDerivAt m m' z)
    (hu : DifferentiableAt ℝ u (m z)) :
    dbarR (fun w => u (m w)) z = (starRingEnd ℂ) m' * dbarR u (m z) := by
  have hc : HasFDerivAt (fun w => u (m w)) ((fderiv ℝ u (m z)).comp
      ((ContinuousLinearMap.toSpanSingleton ℂ m').restrictScalars ℝ)) z :=
    hu.hasFDerivAt.comp z (hm.hasFDerivAt.restrictScalars ℝ)
  rw [dbarR, hc.fderiv, dbarR]
  set L := fderiv ℝ u (m z)
  have key : ∀ v : ℂ, (L v : ℂ) = v.re * L 1 + v.im * L Complex.I := fun v => by
    conv_lhs => rw [← Complex.re_add_im v]
    rw [show (v.re : ℂ) + v.im * Complex.I = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one]]
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    push_cast
    ring
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul]
  rw [key m', key (Complex.I * m')]
  have hconj : (starRingEnd ℂ) m' = (m'.re : ℂ) - (m'.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hconj]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem det_coe_GL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).val.det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp

theorem mob_eq_coe_smul (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    mob γ z = ↑((γ : GL (Fin 2) ℝ) • ofComplex z) := by
  rw [← ModularGroup.sl_moeb, coe_smul, ofComplex_apply_of_im_pos hz]

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) ((denom γ z ^ 2)⁻¹) z := by
  have h := (hasStrictDerivAt_smul (g := (γ : GL (Fin 2) ℝ))
    (by rw [det_coe_GL]; exact one_pos) ⟨z, hz⟩).hasDerivAt
  rw [det_coe_GL, Complex.ofReal_one, one_div] at h
  have hev : mob γ =ᶠ[𝓝 z] fun w => (↑((γ : GL (Fin 2) ℝ) • ofComplex w) : ℂ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw using mob_eq_coe_smul γ hw
  exact h.congr_of_eventuallyEq hev

theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, num, denom]

theorem mob_inv_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : mob γ⁻¹ (mob γ z) = z := by
  have := mob_mob γ⁻¹ γ ⟨z, hz⟩
  rw [inv_mul_cancel, mob_one] at this
  exact this

theorem im_mob_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (mob γ z).im := by
  rw [← coe_smul γ ⟨z, hz⟩]; exact UpperHalfPlane.im_pos _

theorem integral_comp_mob (γ : SL(2, ℤ)) (f : ℂ → ℂ) :
    (∫ z in 𝕌, f z) = ∫ z in 𝕌, (‖denom γ z‖ ^ 4)⁻¹ • f (mob γ z) ∧
    (IntegrableOn f 𝕌 → IntegrableOn (fun z => (‖denom γ z‖ ^ 4)⁻¹ • f (mob γ z)) 𝕌) := by
  set m : ℂ → ℂ := fun z => ↑((γ : GL (Fin 2) ℝ) • ofComplex z) with hm
  have hinj : Set.InjOn m 𝕌 := by
    intro z hz w hw he
    simp only [m, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hw] at he
    have := smul_left_cancel _ (UpperHalfPlane.ext he)
    simpa using congrArg UpperHalfPlane.coe this
  have hderiv : ∀ z ∈ 𝕌, HasFDerivWithinAt m (smulFDeriv (γ : GL (Fin 2) ℝ) z) 𝕌 z :=
    fun z hz => (hasStrictFDerivAt_smul _ ⟨z, hz⟩).hasFDerivAt.hasFDerivWithinAt
  have himage : m '' 𝕌 = 𝕌 := by
    ext w
    constructor
    · rintro ⟨z, -, rfl⟩
      exact UpperHalfPlane.im_pos _
    · intro hw
      refine ⟨↑((γ : GL (Fin 2) ℝ)⁻¹ • (⟨w, hw⟩ : ℍ)), UpperHalfPlane.im_pos _, ?_⟩
      simp only [m, ofComplex_apply, smul_inv_smul]
  have hpt : ∀ z ∈ 𝕌, |(smulFDeriv (γ : GL (Fin 2) ℝ) z).det| • f (m z) =
      (‖denom γ z‖ ^ 4)⁻¹ • f (mob γ z) := fun z hz => by
    have hmz : m z = mob γ z := (mob_eq_coe_smul γ hz).symm
    have h1 : ((γ : GL (Fin 2) ℝ)).det.val = 1 := by simp
    rw [hmz, det_smulFDeriv, h1, sign_one, SignType.coe_one, one_pow, one_mul, one_div,
      abs_of_nonneg (by positivity)]
  have hmeas : MeasurableSet 𝕌 := isOpen_upperHalfPlaneSet.measurableSet
  refine ⟨?_, fun hf => ?_⟩
  · have := integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hderiv hinj f
    rw [himage] at this
    rw [this]
    exact setIntegral_congr_fun hmeas hpt
  · have := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas hderiv hinj f).1
      (by rw [himage]; exact hf)
    exact this.congr_fun hpt hmeas

end Calculus

section Unfolding

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet
local notation "st" => Real.smoothTransition

theorem mem_box {T : ℝ} {z : ℂ} :
    z ∈ box T ↔ z.re ∈ Icc (-1 : ℝ) 1 ∧ z.im ∈ Icc (5 / 8 : ℝ) (T + 4) := Iff.rfl

theorem box_subset (T : ℝ) : box T ⊆ 𝕌 := fun _ hz => im_pos_of_mem_box hz

def gammaOne (T : ℝ) : Finset SL(2, ℤ) :=
  (finite_moving (boxH T) (boxH T) (isCompact_boxH T) (isCompact_boxH T)).toFinset

theorem mem_gammaOne {T : ℝ} {γ : SL(2, ℤ)} {z : ℂ} (hz : z ∈ box T)
    (hγz : mob γ z ∈ box T) : γ ∈ gammaOne T := by
  simp only [gammaOne, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hz0 := im_pos_of_mem_box hz
  refine ⟨γ • ⟨z, hz0⟩, ⟨⟨z, hz0⟩, hz, rfl⟩, ?_⟩
  show ((γ • (⟨z, hz0⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]; exact hγz

theorem inv_mem_gammaOne {T : ℝ} {γ : SL(2, ℤ)} (h : γ ∈ gammaOne T) :
    γ⁻¹ ∈ gammaOne T := by
  simp only [gammaOne, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢
  obtain ⟨_, ⟨τ, hτ, rfl⟩, hL⟩ := h
  exact ⟨τ, ⟨γ • τ, hL, inv_smul_smul γ τ⟩, hτ⟩

theorem sum_pu_mob_eq_one {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ box T)
    (hzT : z.im ≤ T + 3) : ∑ γ ∈ gammaOne T, pu T (mob γ z) = 1 := by
  have hz0 := im_pos_of_mem_box hz
  have h58 : (5 / 8 : ℝ) ≤ z.im := (mem_box.1 hz).2.1
  have hcov : 1 / 2 ≤ cover T ((⟨z, hz0⟩ : ℍ) : ℂ) := by
    refine half_le_cover ⟨z, hz0⟩ hzT ?_
    show z.im⁻¹ ≤ T + 3
    calc z.im⁻¹ ≤ (5 / 8 : ℝ)⁻¹ := by gcongr
      _ ≤ T + 3 := by norm_num; linarith
  refine (finsum_eq_sum_of_support_subset _ fun γ hγ => ?_).symm.trans
    (finsum_pu_mob ⟨z, hz0⟩ hcov)
  exact mem_gammaOne hz (support_bump_subset T (support_pu_subset T hγ))

theorem sum_pu_mob_inv_eq_one {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ box T)
    (hzT : z.im ≤ T + 3) : ∑ γ ∈ gammaOne T, pu T (mob γ⁻¹ z) = 1 := by
  rw [← sum_pu_mob_eq_one hT hz hzT]
  exact Finset.sum_equiv (Equiv.inv _)
    (fun γ => ⟨inv_mem_gammaOne, fun h => by simpa using inv_mem_gammaOne h⟩) (fun γ _ => rfl)

theorem inv_entry (γ : SL(2, ℤ)) : (γ⁻¹ 1 0 : ℤ) = -γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]; rfl

theorem gcut_mob_eq {T : ℝ} (hT : 2 ≤ T) {γ : SL(2, ℤ)} {z : ℂ} (hz : z ∈ box T)
    (hγz : mob γ z ∈ box T) : gcut T (mob γ z) = gcut T z := by
  have hz0 := im_pos_of_mem_box hz
  have him : (mob γ z).im = UpperHalfPlane.im (γ • ⟨z, hz0⟩) := by
    rw [← UpperHalfPlane.coe_im, coe_smul]
  by_cases hc : (γ 1 0 : ℤ) = 0
  · have : (mob γ z).im = z.im := by rw [him, im_smul_of_c_eq_zero γ _ hc]; rfl
    simp only [gcut, this]
  · have h1 : (mob γ z).im ≤ z.im⁻¹ := him ▸ im_smul_le_inv γ _ hc
    have h2 : z.im ≤ (mob γ z).im⁻¹ := by
      have := im_smul_le_inv γ⁻¹ (γ • ⟨z, hz0⟩) (by rwa [inv_entry, neg_ne_zero])
      rwa [inv_smul_smul, ← him] at this
    have hz58 : (5 / 8 : ℝ) ≤ z.im := (mem_box.1 hz).2.1
    have hγ58 : (5 / 8 : ℝ) ≤ (mob γ z).im := (mem_box.1 hγz).2.1
    have hzT : z.im ≤ T :=
      calc z.im ≤ (mob γ z).im⁻¹ := h2
        _ ≤ (5 / 8 : ℝ)⁻¹ := by gcongr
        _ ≤ T := by norm_num; linarith
    have hγT : (mob γ z).im ≤ T :=
      calc (mob γ z).im ≤ z.im⁻¹ := h1
        _ ≤ (5 / 8 : ℝ)⁻¹ := by gcongr
        _ ≤ T := by norm_num; linarith
    rw [gcut_eq_one hzT, gcut_eq_one hγT]

theorem dbarR_pu_mob_eq_zero {T : ℝ} {γ : SL(2, ℤ)} {u : ℂ} (hu : 0 < u.im)
    (h : mob γ u ∉ tsupport (pu T)) : dbarR (fun w => pu T (mob γ w)) u = 0 := by
  have hev : (fun w => pu T (mob γ w)) =ᶠ[𝓝 u] fun _ => 0 := by
    have h1 : ∀ᶠ w in 𝓝 u, mob γ w ∈ (tsupport (pu T))ᶜ :=
      (analyticAt_mob γ hu).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport _).isOpen_compl.mem_nhds h)
    exact h1.mono fun w hw => image_eq_zero_of_notMem_tsupport hw
  rw [dbarR_congr hev]
  simp [dbarR]

theorem sum_dbarR_pu_mob_eq_zero {T : ℝ} (hT : 0 ≤ T) {u : ℂ} (hpu : pu T u ≠ 0)
    (hg : gcut T u ≠ 0) : ∑ γ ∈ gammaOne T, dbarR (fun w => pu T (mob γ w)) u = 0 := by
  have hb : bump T u ≠ 0 := support_pu_subset T hpu
  have hu0 : 0 < u.im := im_pos_of_bump_ne_zero hb
  have huT : u.im < T + 1 := by
    by_contra h; exact hg (gcut_eq_zero (not_lt.1 h))
  rw [← dbarR_sum (gammaOne T) (fun γ w => pu T (mob γ w)) u fun γ _ =>
      ((pu_contDiff T).differentiable one_ne_zero _).comp _
        ((analyticAt_mob γ hu0).differentiableAt.restrictScalars ℝ)]
  have hev : (fun w => ∑ γ ∈ gammaOne T, pu T (mob γ w)) =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
    have hopen : IsOpen {w : ℂ | bump T w ≠ 0 ∧ w.im < T + 3} :=
      (isOpen_ne_fun (bump_contDiff T).continuous continuous_const).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hb, by linarith⟩] with w hw
    exact sum_pu_mob_eq_one hT (support_bump_subset T hw.1) hw.2.le
  rw [dbarR_congr hev]
  simp [dbarR]

theorem continuous_dbarR_pu (T : ℝ) : Continuous (dbarR (pu T)) := by
  have hc : Continuous (fderiv ℝ (pu T)) := (pu_contDiff T).continuous_fderiv one_ne_zero
  exact ((Complex.continuous_ofReal.comp (hc.clm_apply continuous_const)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (hc.clm_apply continuous_const)))).div_const _

theorem integral_unfold_eq_zero {T : ℝ} (hT : 2 ≤ T) (F : ℂ → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (z : ℂ), 0 < z.im → F (mob γ z) = F z * denom γ z ^ 2)
    (hint : ∀ φ : ℂ → ℂ, ContinuousOn φ 𝕌 → Function.support φ ⊆ box T →
      Integrable fun z => F z * φ z) :
    ∫ z, F z * ((gcut T z : ℂ) * dbarR (pu T) z) = 0 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hmeas : MeasurableSet 𝕌 := isOpen_upperHalfPlaneSet.measurableSet
  have hcpu : Continuous (pu T) := (pu_contDiff T).continuous
  have hcd := continuous_dbarR_pu T
  have hcmob : ∀ γ : SL(2, ℤ), ContinuousOn (mob γ) 𝕌 := fun γ z hz =>
    (analyticAt_mob γ hz).continuousAt.continuousWithinAt
  have hsuppd : ∀ z, z ∉ box T → dbarR (pu T) z = 0 := fun z hz =>
    dbarR_of_notMem_tsupport fun h => hz (tsupport_pu_subset T h)
  set Φ : ℂ → ℂ := fun z => F z * ((gcut T z : ℂ) * dbarR (pu T) z) with hΦ
  have hΦ0 : ∀ z, z ∉ box T → Φ z = 0 := fun z hz => by
    simp only [hΦ, hsuppd z hz, mul_zero]

  have h1 : ∀ z, Φ z = ∑ γ ∈ gammaOne T, (pu T (mob γ⁻¹ z) : ℂ) * Φ z := by
    intro z
    rw [← Finset.sum_mul]
    by_cases hz : z ∈ box T
    · by_cases hg : gcut T z = 0
      · have : Φ z = 0 := by simp only [hΦ, hg, Complex.ofReal_zero, zero_mul, mul_zero]
        rw [this, mul_zero]
      · have hzT : z.im ≤ T + 3 := by
          by_contra h
          exact hg (gcut_eq_zero (by push Not at h; linarith))
        have h' : ∑ γ ∈ gammaOne T, (pu T (mob γ⁻¹ z) : ℂ) = 1 := by
          exact_mod_cast sum_pu_mob_inv_eq_one hT0 hz hzT
        rw [h', one_mul]
    · rw [hΦ0 z hz, mul_zero]

  have hint1 : ∀ γ : SL(2, ℤ), Integrable fun z => (pu T (mob γ⁻¹ z) : ℂ) * Φ z := by
    intro γ
    have : (fun z => (pu T (mob γ⁻¹ z) : ℂ) * Φ z) =
        fun z => F z * ((pu T (mob γ⁻¹ z) : ℂ) * ((gcut T z : ℂ) * dbarR (pu T) z)) := by
      ext z; simp only [hΦ]; ring
    rw [this]
    refine hint _ ?_ fun z hz => ?_
    · exact ((Complex.continuous_ofReal.comp hcpu).comp_continuousOn (hcmob γ⁻¹)).mul
        (((Complex.continuous_ofReal.comp (gcut_contDiff T).continuous).mul hcd).continuousOn)
    · by_contra hb
      exact hz (by simp only [hsuppd z hb, mul_zero])

  have step3 : ∀ γ : SL(2, ℤ),
      (∫ z, (pu T (mob γ⁻¹ z) : ℂ) * Φ z) = (∫ u in 𝕌, (pu T u : ℂ) * F u * (gcut T u : ℂ) *
          dbarR (fun w => pu T (mob γ w)) u) ∧
        IntegrableOn (fun u => (pu T u : ℂ) * F u * (gcut T u : ℂ) *
          dbarR (fun w => pu T (mob γ w)) u) 𝕌 := by
    intro γ
    have hzero : ∀ z ∉ 𝕌, (pu T (mob γ⁻¹ z) : ℂ) * Φ z = 0 := fun z hz => by
      rw [hΦ0 z fun h => hz (box_subset T h), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    obtain ⟨hcov, hcovint⟩ := integral_comp_mob γ (fun z => (pu T (mob γ⁻¹ z) : ℂ) * Φ z)
    rw [hcov]
    have hpt : ∀ u ∈ 𝕌, (‖denom γ u‖ ^ 4)⁻¹ • ((pu T (mob γ⁻¹ (mob γ u)) : ℂ) * Φ (mob γ u)) =
        (pu T u : ℂ) * F u * (gcut T u : ℂ) * dbarR (fun w => pu T (mob γ w)) u := by
      intro u hu
      have hu0 : 0 < u.im := hu
      have hd : denom γ u ≠ 0 := denom_ne_zero' γ hu0
      rw [mob_inv_mob γ hu0]
      simp only [hΦ]
      rw [hF γ u hu0]
      have hchain := dbarR_comp (u := pu T) (hasDerivAt_mob γ hu0)
        ((pu_contDiff T).differentiable one_ne_zero _)
      by_cases hpu : pu T u = 0
      · simp [hpu]
      by_cases hdb : dbarR (fun w => pu T (mob γ w)) u = 0
      · have : dbarR (pu T) (mob γ u) = 0 := by
          rw [hdb, eq_comm, mul_eq_zero] at hchain
          rcases hchain with h | h
          · exfalso
            rw [map_eq_zero, inv_eq_zero] at h
            exact hd (pow_eq_zero_iff two_ne_zero |>.1 h)
          · exact h
        simp [this, hdb]
      have hub : u ∈ box T := support_bump_subset T (support_pu_subset T hpu)
      have hγub : mob γ u ∈ box T := by
        by_contra h
        exact hdb (dbarR_pu_mob_eq_zero hu0 fun h' => h (tsupport_pu_subset T h'))
      rw [gcut_mob_eq hT hub hγub]
      have hX : dbarR (pu T) (mob γ u) =
          (starRingEnd ℂ) (denom γ u ^ 2) * dbarR (fun w => pu T (mob γ w)) u := by
        rw [hchain, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero 2 hd), map_one, one_mul]
      rw [hX, Complex.real_smul]
      have h4 : denom γ u ^ 2 * (starRingEnd ℂ) (denom γ u ^ 2) = ((‖denom γ u‖ ^ 4 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
      have hkey : (((‖denom γ u‖ ^ 4)⁻¹ : ℝ) : ℂ) *
          (denom γ u ^ 2 * (starRingEnd ℂ) (denom γ u ^ 2)) = 1 := by
        rw [h4, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 4 (norm_ne_zero_iff.2 hd)),
          Complex.ofReal_one]
      linear_combination
        ((pu T u : ℂ) * F u * (gcut T u : ℂ) * dbarR (fun w => pu T (mob γ w)) u) * hkey
    exact ⟨setIntegral_congr_fun hmeas hpt,
      ((hcovint (hint1 γ).integrableOn).congr_fun hpt hmeas)⟩

  have step5 : ∀ u ∈ 𝕌, ∑ γ ∈ gammaOne T, (pu T u : ℂ) * F u * (gcut T u : ℂ) *
      dbarR (fun w => pu T (mob γ w)) u = 0 := by
    intro u _
    rw [← Finset.mul_sum]
    by_cases hpu : pu T u = 0
    · simp [hpu]
    by_cases hg : gcut T u = 0
    · simp [hg]
    rw [sum_dbarR_pu_mob_eq_zero hT0 hpu hg, mul_zero]
  calc ∫ z, Φ z = ∫ z, ∑ γ ∈ gammaOne T, (pu T (mob γ⁻¹ z) : ℂ) * Φ z :=
        integral_congr_ae (Eventually.of_forall h1)
    _ = ∑ γ ∈ gammaOne T, ∫ z, (pu T (mob γ⁻¹ z) : ℂ) * Φ z :=
        integral_finsetSum _ fun γ _ => hint1 γ
    _ = ∑ γ ∈ gammaOne T, ∫ u in 𝕌, (pu T u : ℂ) * F u * (gcut T u : ℂ) *
          dbarR (fun w => pu T (mob γ w)) u :=
        Finset.sum_congr rfl fun γ _ => (step3 γ).1
    _ = ∫ u in 𝕌, ∑ γ ∈ gammaOne T, (pu T u : ℂ) * F u * (gcut T u : ℂ) *
          dbarR (fun w => pu T (mob γ w)) u :=
        (integral_finsetSum _ fun γ _ => (step3 γ).2).symm
    _ = ∫ u in 𝕌, (0 : ℂ) := setIntegral_congr_fun hmeas step5
    _ = 0 := by simp

end Unfolding

section Strip

local notation "st" => Real.smoothTransition

def iota (q : ℤ × Bool) : SL(2, ℤ) :=
  if q.2 then ModularGroup.T ^ q.1 else -(ModularGroup.T ^ q.1)

theorem iota_entries (m : ℤ) (b : Bool) :
    ((iota (m, b)) 1 0 : ℤ) = 0 ∧ ((iota (m, b)) 0 1 : ℤ) * (iota (m, b)) 1 1 = m ∧
      ((iota (m, b)) 0 0 : ℤ) = (if b then 1 else -1) := by
  cases b <;> simp [iota, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg]

theorem iota_injective : Function.Injective iota := by
  rintro ⟨m, b⟩ ⟨m', b'⟩ h
  obtain ⟨-, h2, h3⟩ := iota_entries m b
  obtain ⟨-, h2', h3'⟩ := iota_entries m' b'
  rw [h] at h2 h3
  have hm : m = m' := h2.symm.trans h2'
  have hb : (if b then (1 : ℤ) else -1) = if b' then 1 else -1 := h3.symm.trans h3'
  have hb' : b = b' := by
    cases b <;> cases b' <;> first | rfl | (exfalso; norm_num at hb)
  rw [hm, hb']

theorem exists_iota_eq (γ : SL(2, ℤ)) (hc : (γ 1 0 : ℤ) = 0) : ∃ q : ℤ × Bool, iota q = γ := by
  obtain ⟨had, hdd⟩ := d_sq_of_c_eq_zero γ hc
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdd with ⟨h1, -⟩ | ⟨h1, -⟩
  · have ha : (γ 0 0 : ℤ) = 1 := by rw [h1, mul_one] at had; exact had
    refine ⟨(γ 0 1, true), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iota, ModularGroup.coe_T_zpow, ha, h1, hc]
  · have ha : (γ 0 0 : ℤ) = -1 := by rw [h1] at had; linarith
    refine ⟨(-(γ 0 1), false), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [iota, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg, ha, h1, hc]

theorem cover_eq_two {T : ℝ} (hT : 2 ≤ T) (τ : ℍ) (h1 : T ≤ τ.im) (h2 : τ.im ≤ T + 3) :
    cover T τ = 2 := by
  have hc0 : ∀ γ : SL(2, ℤ), bump T (mob γ τ) ≠ 0 → (γ 1 0 : ℤ) = 0 := by
    intro γ hγ
    by_contra hc
    have him := im_smul_le_inv γ τ hc
    have h58 := (mem_of_bump_ne_zero hγ).2.1
    rw [← coe_smul, UpperHalfPlane.coe_im] at h58
    have : τ.im⁻¹ ≤ 2⁻¹ := by
      rw [inv_le_inv₀ τ.im_pos two_pos]; linarith
    linarith
  have hval : ∀ q : ℤ × Bool, bump T (mob (iota q) τ) = pOne (τ.re + q.1) := by
    rintro ⟨m, b⟩
    obtain ⟨hc, hbd, -⟩ := iota_entries m b
    rw [← coe_smul, coe_smul_of_c_eq_zero _ τ hc, hbd, bump]
    simp only [Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    rw [pTwo_eq_one (by linarith) h2, mul_one]
  unfold cover
  set s : Finset (ℤ × Bool) := {⌊-τ.re⌋, ⌊-τ.re⌋ + 1} ×ˢ Finset.univ with hs
  rw [finsum_eq_sum_of_support_subset (s := s.image iota)]
  · rw [Finset.sum_image fun q _ q' _ h => iota_injective h, Finset.sum_product]
    simp_rw [hval]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
    rw [Finset.sum_pair (by omega)]
    have := pOne_floor_add τ.re
    linarith
  · intro γ hγ
    obtain ⟨q, rfl⟩ := exists_iota_eq γ (hc0 γ hγ)
    have hq : pOne (τ.re + q.1) ≠ 0 := by rw [← hval]; exact hγ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨q, ?_, rfl⟩
    simp only [hs, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_insert,
      Finset.mem_singleton]
    exact eq_floor_of_pOne_ne_zero τ.re q.1 hq

theorem recip_two : recip 2 = 1 / 2 := by
  rw [recip, Real.smoothTransition.one_of_one_le (by norm_num)]

theorem pu_eq_of_mem_strip {T : ℝ} (hT : 2 ≤ T) {z : ℂ} (h1 : T ≤ z.im) (h2 : z.im ≤ T + 3) :
    pu T z = pOne z.re / 2 := by
  have hz : 0 < z.im := by linarith
  have hcov : cover T z = 2 := cover_eq_two hT ⟨z, hz⟩ h1 h2
  rw [pu, hcov, bump, pTwo_eq_one (by linarith) h2, mul_one, recip_two]
  ring

theorem dbarR_gcut (T : ℝ) (z : ℂ) :
    dbarR (gcut T) z = -(Complex.I / 2) * (deriv st (z.im - T) : ℝ) := by
  rw [dbarR, fderiv_gcut_one, fderiv_gcut_I]; push_cast; ring

theorem strip_integrand {T : ℝ} (hT : 2 ≤ T) (F : ℂ → ℂ) (z : ℂ) :
    F z * ((pu T z : ℂ) * dbarR (gcut T) z) =
      -(Complex.I / 4) * (F z * (pOne z.re * deriv st (z.im - T) : ℝ)) := by
  rw [dbarR_gcut]
  by_cases hd : deriv st (z.im - T) = 0
  · simp [hd]
  · obtain ⟨h1, h2⟩ := mem_Ioo_of_deriv_st_ne_zero hd
    rw [pu_eq_of_mem_strip hT (by linarith) (by linarith)]
    push_cast; ring

end Strip

section Main

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet
local notation "st" => Real.smoothTransition

theorem ofComplex_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ofComplex (mob γ z) = γ • (⟨z, hz⟩ : ℍ) := by
  have h := congrArg ofComplex (coe_smul γ ⟨z, hz⟩)
  rw [ofComplex_apply] at h
  exact h.symm

theorem tendsto_zero_of_isBigO_exp {ω : ℍ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hO : ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) : Tendsto ω atImInfty (𝓝 0) := by
  refine hO.trans_tendsto ?_
  have him : Tendsto UpperHalfPlane.im atImInfty atTop := Filter.tendsto_comap
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (him.const_mul_atTop hδ)).congr fun τ => ?_
  simp [neg_mul]

theorem main (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∃ δ : ℝ, 0 < δ ∧ ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer SL(2, ℤ) σ) = 0 := by
  classical

  set B : ℝ := ∑ σ ∈ S, (σ.im + σ.im⁻¹) with hB
  have hBσ : ∀ σ ∈ S, σ.im ≤ B ∧ σ.im⁻¹ ≤ B := fun σ hσ => by
    have h := Finset.single_le_sum (s := S) (f := fun σ : ℍ => σ.im + σ.im⁻¹)
      (fun σ _ => by positivity) hσ
    have h1 := σ.im_pos
    have h2 := inv_pos.2 σ.im_pos
    exact ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun σ _ => by positivity
  have hpoleB : ∀ τ : ℍ, c τ ≠ 0 → τ.im ≤ B := by
    intro τ hτ
    obtain ⟨σ, hσ, γ, rfl⟩ := hS τ hτ
    obtain ⟨h1, h2⟩ := hBσ σ hσ
    exact (im_smul_le_max γ σ).trans (max_le h1 h2)
  set T : ℝ := B + 2 with hT
  have hT2 : (2 : ℝ) ≤ T := by linarith

  have hcs : ∀ (γ : SL(2, ℤ)) (τ : ℍ), c (γ • τ) = c τ := fun γ τ => residue_smul hΓ hloc γ τ
  set F : ℂ → ℂ := fun z => ω (ofComplex z) with hF
  set cC : ℂ → ℂ := fun a => c (ofComplex a) with hcC
  have hlocU : ∀ a ∈ 𝕌, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = cC a / (z - a) + g z := by
    intro a ha
    obtain ⟨g, hg, hev⟩ := hloc ⟨a, ha⟩
    refine ⟨g, hg, ?_⟩
    simp only [hcC, ofComplex_apply_of_im_pos ha]
    exact hev
  have hFmob : ∀ (γ : SL(2, ℤ)) (z : ℂ), 0 < z.im → F (mob γ z) = F z * denom γ z ^ 2 := by
    intro γ z hz
    simp only [hF]
    rw [ofComplex_mob γ hz, apply_smul hΓ γ ⟨z, hz⟩, ofComplex_apply_of_im_pos hz]

  have hFbox : IntegrableOn F (box T) :=
    (Complex.locallyIntegrableOn_of_simplePoles 𝕌 isOpen_upperHalfPlaneSet F cC hlocU)
      |>.integrableOn_compact_subset (box_subset T) (isCompact_box T)
  have hint : ∀ φ : ℂ → ℂ, ContinuousOn φ 𝕌 → Function.support φ ⊆ box T →
      Integrable fun z => F z * φ z := by
    intro φ hφ hφs
    have h1 : IntegrableOn (fun z => F z * φ z) (box T) :=
      hFbox.mul_continuousOn (hφ.mono (box_subset T)) (isCompact_box T)
    exact (integrableOn_iff_integrable_of_support_subset fun z hz =>
      hφs (Function.support_mul_subset_right _ _ hz)).1 h1

  set hr : ℂ → ℝ := fun z => pu T z * gcut T z with hhr
  set h : ℂ → ℂ := fun z => (hr z : ℂ) with hh
  have hpu_box : ∀ z, pu T z ≠ 0 → z ∈ box T := fun z hz =>
    support_bump_subset T (support_pu_subset T hz)
  have hr_supp : Function.support hr ⊆ box T := fun z hz =>
    hpu_box z (left_ne_zero_of_mul hz)
  have hhC : ContDiff ℝ 1 h :=
    Complex.ofRealCLM.contDiff.comp ((pu_contDiff T).mul (gcut_contDiff T))
  have hhsupp : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_box T) fun z hz => ?_
    have h0 : hr z = 0 := by_contra fun h' => hz (hr_supp h')
    simp only [hh, h0, Complex.ofReal_zero]
  have htsupp : tsupport h ⊆ 𝕌 := by
    refine (closure_minimal ?_ (isClosed_box T)).trans (box_subset T)
    intro z hz
    exact hr_supp fun h' => hz (by simp only [hh, h', Complex.ofReal_zero])

  have hE := Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue 𝕌 isOpen_upperHalfPlaneSet
    F cC hlocU h hhC hhsupp htsupp
  have hdpu : Differentiable ℝ (pu T) := (pu_contDiff T).differentiable one_ne_zero
  have hdg : Differentiable ℝ (gcut T) := (gcut_contDiff T).differentiable one_ne_zero
  have hlhs : ∀ z, F z * ((fderiv ℝ h z 1 + Complex.I * fderiv ℝ h z Complex.I) / 2) =
      F z * ((pu T z : ℂ) * dbarR (gcut T) z) + F z * ((gcut T z : ℂ) * dbarR (pu T) z) := by
    intro z
    have hd : DifferentiableAt ℝ hr z := (hdpu z).mul (hdg z)
    rw [hh, dbar_ofReal hd, hhr, dbarR_mul (hdpu z) (hdg z)]
    ring
  have hcont_st : Continuous fun z : ℂ => deriv st (z.im - T) :=
    continuous_deriv_st.comp (Complex.continuous_im.sub continuous_const)
  have hint_a : Integrable fun z => F z * ((pu T z : ℂ) * dbarR (gcut T) z) := by
    refine hint _ (Continuous.continuousOn ?_) fun z hz => hpu_box z fun h0 => hz ?_
    · have : (fun z => (pu T z : ℂ) * dbarR (gcut T) z) =
          fun z => (pu T z : ℂ) * (-(Complex.I / 2) * (deriv st (z.im - T) : ℝ)) :=
        funext fun z => by rw [dbarR_gcut]
      rw [this]
      exact (Complex.continuous_ofReal.comp (pu_contDiff T).continuous).mul
        (continuous_const.mul (Complex.continuous_ofReal.comp hcont_st))
    · simp [h0]
  have hint_b : Integrable fun z => F z * ((gcut T z : ℂ) * dbarR (pu T) z) := by
    refine hint _ (Continuous.continuousOn ?_) fun z hz => ?_
    · exact (Complex.continuous_ofReal.comp (gcut_contDiff T).continuous).mul
        (continuous_dbarR_pu T)
    · by_contra hb
      refine hz ?_
      show (gcut T z : ℂ) * dbarR (pu T) z = 0
      rw [dbarR_of_notMem_tsupport fun h' => hb (tsupport_pu_subset T h'), mul_zero]

  have hI1 : ∫ z, F z * ((gcut T z : ℂ) * dbarR (pu T) z) = 0 :=
    integral_unfold_eq_zero hT2 F hFmob hint

  obtain ⟨δ, hδ, hO⟩ := hcusp
  have hhol : ∀ τ : ℍ, B < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z := by
    intro τ hτ
    have hc0 : c τ = 0 := by_contra fun h' => (not_le.2 hτ) (hpoleB τ h')
    obtain ⟨g, hg, hev⟩ := hloc τ
    exact ⟨g, hg, hev.mono fun z hz => by rw [hz, hc0, zero_div, zero_add]⟩
  have hρ : Function.support (fun y : ℝ => deriv st (y - T)) ⊆ Set.Ioi B := by
    intro y hy
    have hy' : deriv st (y - T) ≠ 0 := hy
    have := (mem_Ioo_of_deriv_st_ne_zero hy').1
    show B < y
    linarith
  have hint2 : Integrable fun z => F z * ((pOne z.re * deriv st (z.im - T) : ℝ) : ℂ) := by
    refine hint _ (Continuous.continuousOn ?_) fun z hz => ?_
    · exact Complex.continuous_ofReal.comp
        ((pOne_contDiff.continuous.comp Complex.continuous_re).mul hcont_st)
    · have h1 : pOne z.re ≠ 0 := fun h0 => hz (by simp [h0])
      have h2 : deriv st (z.im - T) ≠ 0 := fun h0 => hz (by simp [h0])
      obtain ⟨ha, hb⟩ := mem_Ioo_of_pOne_ne_zero h1
      obtain ⟨hc', hd⟩ := mem_Ioo_of_deriv_st_ne_zero h2
      exact ⟨⟨ha.le, hb.le⟩, by constructor <;> linarith⟩
  have hI2' : ∫ z, F z * ((pOne z.re * deriv st (z.im - T) : ℝ) : ℂ) = 0 :=
    UpperHalfPlane.integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty ω B hB0
      (apply_vadd_one hΓ) (tendsto_zero_of_isBigO_exp hδ hO) hhol pOne
      (fun y => deriv st (y - T)) (fun x hx => mem_Ioo_of_pOne_ne_zero hx)
      (fun x hx => pOne_sub_one_add hx.1 hx.2) hρ hint2
  have hI2 : ∫ z, F z * ((pu T z : ℂ) * dbarR (gcut T) z) = 0 := by
    simp_rw [strip_integrand hT2 F]
    rw [integral_const_mul, hI2', mul_zero]

  have hfin : {a ∈ box T | c (ofComplex a) ≠ 0}.Finite :=
    finite_poles hloc (isCompact_box T) (box_subset T)
  have h2 : ∀ σ ∈ S, c σ ≠ 0 → ∑ᶠ γ : SL(2, ℤ), hr (mob γ σ) = 1 := by
    intro σ hσ _
    obtain ⟨hσ1, hσ2⟩ := hBσ σ hσ
    have hcov : 1 / 2 ≤ cover T σ := half_le_cover σ (by linarith) (by linarith)
    rw [← finsum_pu_mob σ hcov]
    refine finsum_congr fun γ => ?_
    have hle : (mob γ σ).im ≤ T := by
      rw [← coe_smul, UpperHalfPlane.coe_im]
      exact (im_smul_le_max γ σ).trans ((max_le hσ1 hσ2).trans (by linarith))
    simp only [hhr, gcut_eq_one hle, mul_one]
  have hpole : ∑ᶠ a : ℂ, cC a * h a = ∑ σ ∈ S, c σ / Nat.card (stabilizer SL(2, ℤ) σ) :=
    finsum_residue_mul_eq hfin hcs hS hinj hr_supp h2

  have hLHS : ∫ z, F z * ((fderiv ℝ h z 1 + Complex.I * fderiv ℝ h z Complex.I) / 2) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hlhs), integral_add hint_a hint_b, hI1, hI2,
      add_zero]
  rw [hLHS, hpole] at hE
  have hπ : (-(π : ℂ)) ≠ 0 := neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  exact (mul_eq_zero.1 hE.symm).resolve_left hπ

end Main

end LevelOneResidue
p2m_reactivate "P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.LevelOneResidue"

end
p2m_reactivate "P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.LevelOneResidue"

open UpperHalfPlane in
open scoped MatrixGroups Topology ModularForm in
theorem solution
    (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∃ δ : ℝ, 0 < δ ∧ ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer SL(2, ℤ) σ) = 0 :=
  LevelOneResidue.main ω c S hΓ hcusp hloc hS hinj

end S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero
end P2MW
export P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero (solution)
