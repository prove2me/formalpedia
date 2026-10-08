-- Prove2me | solution 1 for TeschlQM.OneParticle.positivityImproving_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T14:27:51.393124+00:00
-- url     : https://prove2.me/submissions/2879bd4d-7bae-45b0-999f-718a3eb195ca

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_positivity

open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open TeschlQM.OneParticle

namespace PFAux

variable {n : ℕ}

/-- Apply a pointwise contraction `T : ℂ → ℂ` to an `L²` function. -/
noncomputable def mapL2 (T : ℂ → ℂ) (hT : Continuous T) (hle : ∀ z, ‖T z‖ ≤ ‖z‖)
    (f : L2 n) : L2 n :=
  (MemLp.of_le (Lp.memLp f) (hT.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => hle (f x))).toLp (fun x => T (f x))

lemma coeFn_mapL2 (T : ℂ → ℂ) (hT : Continuous T) (hle : ∀ z, ‖T z‖ ≤ ‖z‖) (f : L2 n) :
    (mapL2 T hT hle f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fun x => T (f x) :=
  MemLp.coeFn_toLp _

/-- Positivity improving operators are positivity preserving. -/
lemma posPres {A : L2 n →L[ℂ] L2 n} (hpos : IsPositivityImproving A) {f : L2 n}
    (hf : ∀ᵐ x ∂volume, 0 ≤ (f : EuclideanSpace ℝ (Fin n) → ℂ) x) :
    ∀ᵐ x ∂volume, 0 ≤ ((A f : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) x := by
  by_cases h0 : f = 0
  · subst h0
    simp only [map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    rw [hx]
    rfl
  · filter_upwards [hpos f ⟨hf, h0⟩] with x hx using hx.le

lemma re_inner_eq_integral (f g : L2 n) :
    (⟪f, g⟫_ℂ).re = ∫ x, (⟪(f : EuclideanSpace ℝ (Fin n) → ℂ) x, g x⟫_ℂ).re := by
  rw [MeasureTheory.L2.inner_def]
  exact (integral_re (L2.integrable_inner (𝕜 := ℂ) f g)).symm

lemma re_inner_pt (a b : ℂ) : (⟪a, b⟫_ℂ).re = a.re * b.re + a.im * b.im := by
  simp
  ring

lemma re_inner_nonneg {f g : L2 n}
    (hf : ∀ᵐ x ∂volume, 0 ≤ (f : EuclideanSpace ℝ (Fin n) → ℂ) x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) :
    0 ≤ (⟪f, g⟫_ℂ).re := by
  rw [re_inner_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hx hy
  rw [Complex.nonneg_iff] at hx hy
  show 0 ≤ _
  rw [re_inner_pt, ← hx.2]
  nlinarith [hx.1, hy.1]

lemma re_inner_pos {f g : L2 n}
    (hf : ∀ᵐ x ∂volume, 0 < (f : EuclideanSpace ℝ (Fin n) → ℂ) x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ (g : EuclideanSpace ℝ (Fin n) → ℂ) x) (hg0 : g ≠ 0) :
    0 < (⟪f, g⟫_ℂ).re := by
  have hnn : 0 ≤ᵐ[volume] fun x => (⟪(f : EuclideanSpace ℝ (Fin n) → ℂ) x, g x⟫_ℂ).re := by
    filter_upwards [hf, hg] with x hx hy
    rw [Complex.pos_iff] at hx
    rw [Complex.nonneg_iff] at hy
    show 0 ≤ _
    rw [re_inner_pt, ← hx.2]
    nlinarith [hx.1, hy.1]
  have hint : Integrable (fun x => (⟪(f : EuclideanSpace ℝ (Fin n) → ℂ) x, g x⟫_ℂ).re)
      volume := (L2.integrable_inner (𝕜 := ℂ) f g).re
  rw [re_inner_eq_integral]
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) (fun h => hg0 ?_)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h.symm
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hz, hf, hg] with x h0 hx hy
  rw [Complex.pos_iff] at hx
  rw [Complex.nonneg_iff] at hy
  simp only [Pi.zero_apply] at h0 ⊢
  rw [re_inner_pt, ← hx.2, zero_mul, add_zero] at h0
  have hre : (g x).re = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · linarith [hx.1]
    · exact h
  apply Complex.ext
  · simpa using hre
  · simpa using hy.2.symm

/-- An `L²` function is real if its values are a.e. real. -/
def IsRealL2 (f : L2 n) : Prop :=
  ∀ᵐ x ∂volume, ((f : EuclideanSpace ℝ (Fin n) → ℂ) x).im = 0

/-- Real part of an `L²` function. -/
noncomputable def reL2 (f : L2 n) : L2 n :=
  mapL2 (fun z => (z.re : ℂ)) (by fun_prop) (fun z => by simpa using Complex.abs_re_le_norm z) f

/-- Imaginary part of an `L²` function. -/
noncomputable def imL2 (f : L2 n) : L2 n :=
  mapL2 (fun z => (z.im : ℂ)) (by fun_prop) (fun z => by simpa using Complex.abs_im_le_norm z) f

lemma coeFn_reL2 (f : L2 n) :
    (reL2 f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fun x => ((f x).re : ℂ) :=
  coeFn_mapL2 _ _ _ f

lemma coeFn_imL2 (f : L2 n) :
    (imL2 f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fun x => ((f x).im : ℂ) :=
  coeFn_mapL2 _ _ _ f

lemma reL2_real (f : L2 n) : IsRealL2 (reL2 f) := by
  filter_upwards [coeFn_reL2 f] with x hx
  rw [hx]
  simp

lemma imL2_real (f : L2 n) : IsRealL2 (imL2 f) := by
  filter_upwards [coeFn_imL2 f] with x hx
  rw [hx]
  simp

lemma re_add_im (f : L2 n) : reL2 f + Complex.I • imL2 f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (reL2 f) (Complex.I • imL2 f),
    Lp.coeFn_smul Complex.I (imL2 f), coeFn_reL2 f, coeFn_imL2 f] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  apply Complex.ext <;> simp

lemma reL2_of_real {g h : L2 n} (hg : IsRealL2 g) (hh : IsRealL2 h) :
    reL2 (g + Complex.I • h) = g := by
  apply Lp.ext
  filter_upwards [coeFn_reL2 (g + Complex.I • h), Lp.coeFn_add g (Complex.I • h),
    Lp.coeFn_smul Complex.I h, hg, hh] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp [h4, h5]

lemma imL2_of_real {g h : L2 n} (hg : IsRealL2 g) (hh : IsRealL2 h) :
    imL2 (g + Complex.I • h) = h := by
  apply Lp.ext
  filter_upwards [coeFn_imL2 (g + Complex.I • h), Lp.coeFn_add g (Complex.I • h),
    Lp.coeFn_smul Complex.I h, hg, hh] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp [h4, h5]

lemma eig_re_im {A : L2 n →L[ℂ] L2 n} (hreal : IsRealOperator A) {a : ℝ} {f : L2 n}
    (hf : A f = (a : ℂ) • f) :
    A (reL2 f) = (a : ℂ) • reL2 f ∧ A (imL2 f) = (a : ℂ) • imL2 f := by
  have hAr : IsRealL2 (A (reL2 f)) := hreal (reL2 f) (reL2_real f)
  have hAi : IsRealL2 (A (imL2 f)) := hreal (imL2 f) (imL2_real f)
  have hdec : A f = A (reL2 f) + Complex.I • A (imL2 f) := by
    conv_lhs => rw [← re_add_im f]
    rw [map_add, map_smul]
  have h1 : reL2 (A f) = A (reL2 f) := by rw [hdec]; exact reL2_of_real hAr hAi
  have h2 : imL2 (A f) = A (imL2 f) := by rw [hdec]; exact imL2_of_real hAr hAi
  have h3 : reL2 ((a : ℂ) • f) = (a : ℂ) • reL2 f := by
    apply Lp.ext
    filter_upwards [coeFn_reL2 ((a : ℂ) • f), Lp.coeFn_smul (a : ℂ) f,
      Lp.coeFn_smul (a : ℂ) (reL2 f), coeFn_reL2 f] with x e1 e2 e3 e4
    rw [e1, e3, Pi.smul_apply, e4, e2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    apply Complex.ext <;> simp
  have h4 : imL2 ((a : ℂ) • f) = (a : ℂ) • imL2 f := by
    apply Lp.ext
    filter_upwards [coeFn_imL2 ((a : ℂ) • f), Lp.coeFn_smul (a : ℂ) f,
      Lp.coeFn_smul (a : ℂ) (imL2 f), coeFn_imL2 f] with x e1 e2 e3 e4
    rw [e1, e3, Pi.smul_apply, e4, e2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    apply Complex.ext <;> simp
  exact ⟨by rw [← h1, hf, h3], by rw [← h2, hf, h4]⟩

/-- Positive part of the real part of an `L²` function. -/
noncomputable def posL2 (f : L2 n) : L2 n :=
  mapL2 (fun z => ((max z.re 0 : ℝ) : ℂ)) (by fun_prop) (fun z => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (Complex.re_le_norm z) (norm_nonneg z)) f

/-- Negative part of the real part of an `L²` function. -/
noncomputable def negL2 (f : L2 n) : L2 n :=
  mapL2 (fun z => ((max (-z.re) 0 : ℝ) : ℂ)) (by fun_prop) (fun z => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [Complex.abs_re_le_norm z, neg_abs_le z.re]) (norm_nonneg z)) f

lemma coeFn_posL2 (f : L2 n) :
    (posL2 f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fun x => ((max (f x).re 0 : ℝ) : ℂ) :=
  coeFn_mapL2 _ _ _ f

lemma coeFn_negL2 (f : L2 n) :
    (negL2 f : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume]
      fun x => ((max (-(f x).re) 0 : ℝ) : ℂ) :=
  coeFn_mapL2 _ _ _ f

/-- Real eigenfunctions for the eigenvalue `‖A‖` do not change sign. -/
lemma real_eig_sign {A : L2 n →L[ℂ] L2 n} (hpos : IsPositivityImproving A) {η : L2 n}
    (hηr : IsRealL2 η) (hη : A η = (‖A‖ : ℂ) • η) :
    (∀ᵐ x ∂volume, 0 ≤ (η : EuclideanSpace ℝ (Fin n) → ℂ) x) ∨
      (∀ᵐ x ∂volume, 0 ≤ ((-η : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) x) := by
  set p := posL2 η with hpdef
  set m := negL2 η with hmdef
  have hp_nn : ∀ᵐ x ∂volume, 0 ≤ (p : EuclideanSpace ℝ (Fin n) → ℂ) x := by
    filter_upwards [coeFn_posL2 η] with x hx
    rw [hx]
    exact_mod_cast le_max_right _ _
  have hm_nn : ∀ᵐ x ∂volume, 0 ≤ (m : EuclideanSpace ℝ (Fin n) → ℂ) x := by
    filter_upwards [coeFn_negL2 η] with x hx
    rw [hx]
    exact_mod_cast le_max_right _ _
  have hdecomp : η = p - m := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub p m, coeFn_posL2 η, coeFn_negL2 η, hηr] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3]
    apply Complex.ext
    · simp
    · simp [h4]
  have hnorm : ‖p + m‖ ≤ ‖η‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_add p m, coeFn_posL2 η, coeFn_negL2 η] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      max_zero_add_max_neg_zero_eq_abs_self, abs_abs]
    exact Complex.abs_re_le_norm _
  have hAp := posPres hpos hp_nn
  have hAm := posPres hpos hm_nn
  have hc1 := re_inner_nonneg hp_nn hAm
  have hc2 := re_inner_nonneg hm_nn hAp
  have hbound : (⟪p + m, A (p + m)⟫_ℂ).re ≤ ‖A‖ * ‖η‖ ^ 2 := by
    have h1 : (⟪p + m, A (p + m)⟫_ℂ).re ≤ ‖p + m‖ * ‖A (p + m)‖ := by
      simpa using re_inner_le_norm (𝕜 := ℂ) (p + m) (A (p + m))
    have h2 := A.le_opNorm (p + m)
    calc (⟪p + m, A (p + m)⟫_ℂ).re ≤ ‖p + m‖ * ‖A (p + m)‖ := h1
      _ ≤ ‖p + m‖ * (‖A‖ * ‖p + m‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖A‖ * ‖p + m‖ ^ 2 := by ring
      _ ≤ ‖A‖ * ‖η‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (norm_nonneg _)
  have heq : (⟪η, A η⟫_ℂ).re = ‖A‖ * ‖η‖ ^ 2 := by
    rw [hη, inner_smul_right, Complex.re_ofReal_mul,
      show (⟪η, η⟫_ℂ).re = ‖η‖ ^ 2 by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) η]
  have hid : ⟪p + m, A (p + m)⟫_ℂ - ⟪η, A η⟫_ℂ = 2 * (⟪p, A m⟫_ℂ + ⟪m, A p⟫_ℂ) := by
    rw [hdecomp]
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right]
    ring
  have hsum : (⟪p, A m⟫_ℂ).re + (⟪m, A p⟫_ℂ).re ≤ 0 := by
    have := congrArg Complex.re hid
    simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.add_im] at this
    norm_num at this
    rw [map_add] at hbound
    linarith
  by_cases hp0 : p = 0
  · right
    have : -η = m := by rw [hdecomp, hp0]; simp
    rw [this]
    exact hm_nn
  by_cases hm0 : m = 0
  · left
    have : η = p := by rw [hdecomp, hm0]; simp
    rw [this]
    exact hp_nn
  exfalso
  have hpi := re_inner_pos (hpos p ⟨hp_nn, hp0⟩) hm_nn hm0
  rw [← inner_conj_symm (A p) m, Complex.conj_re] at hpi
  linarith

/-- A real eigenfunction for `‖A‖` is a real multiple of a strictly positive one. -/
lemma real_eig_mul {A : L2 n →L[ℂ] L2 n} (hpos : IsPositivityImproving A) {φ ζ : L2 n}
    (hφr : IsRealL2 φ) (hφsp : ∀ᵐ x ∂volume, 0 < (φ : EuclideanSpace ℝ (Fin n) → ℂ) x)
    (hφ : A φ = (‖A‖ : ℂ) • φ) (hφ0 : φ ≠ 0)
    (hζr : IsRealL2 ζ) (hζ : A ζ = (‖A‖ : ℂ) • ζ) : ∃ t : ℝ, ζ = (t : ℂ) • φ := by
  set t : ℝ := (⟪φ, ζ⟫_ℂ).re / (⟪φ, φ⟫_ℂ).re with ht
  refine ⟨t, ?_⟩
  set ξ := ζ - (t : ℂ) • φ with hξdef
  have hξr : IsRealL2 ξ := by
    filter_upwards [hζr, hφr, Lp.coeFn_sub ζ ((t : ℂ) • φ), Lp.coeFn_smul (t : ℂ) φ]
      with x h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h4, Pi.smul_apply, smul_eq_mul]
    simp [h1, h2]
  have hξ : A ξ = (‖A‖ : ℂ) • ξ := by
    rw [hξdef, map_sub, map_smul, hζ, hφ, smul_sub, smul_comm]
  have hφφ : 0 < (⟪φ, φ⟫_ℂ).re := by
    rw [show (⟪φ, φ⟫_ℂ).re = ‖φ‖ ^ 2 by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) φ]
    exact pow_pos (norm_pos_iff.mpr hφ0) 2
  have hre : (⟪φ, ξ⟫_ℂ).re = 0 := by
    rw [hξdef, inner_sub_right, inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul, ht]
    field_simp
    ring
  by_contra hne
  have hξ0 : ξ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  rcases real_eig_sign hpos hξr hξ with h | h
  · have := re_inner_pos hφsp h hξ0
    linarith
  · have := re_inner_pos hφsp h (neg_ne_zero.mpr hξ0)
    rw [inner_neg_right, Complex.neg_re] at this
    linarith

end PFAux

theorem solution (n : ℕ) (A : L2 n →L[ℂ] L2 n) (_hA : IsSelfAdjoint A)
    (hpos : IsPositivityImproving A) (hreal : IsRealOperator A)
    (heig : ∃ ψ : L2 n, ψ ≠ 0 ∧ A ψ = (‖A‖ : ℂ) • ψ) :
    Module.finrank ℂ (Module.End.eigenspace (A : Module.End ℂ (L2 n)) (‖A‖ : ℂ)) = 1 ∧
      ∃ ψ : L2 n, A ψ = (‖A‖ : ℂ) • ψ ∧ TeschlQM.OneParticle.IsStrictlyPositive ψ := by
  classical
  obtain ⟨ψ, hψ0, hψ⟩ := heig
  obtain ⟨hRe, hIm⟩ := PFAux.eig_re_im hreal hψ
  have hex : ∃ η : L2 n, η ≠ 0 ∧ PFAux.IsRealL2 η ∧ A η = (‖A‖ : ℂ) • η := by
    by_cases hr : PFAux.reL2 ψ = 0
    · refine ⟨PFAux.imL2 ψ, ?_, PFAux.imL2_real ψ, hIm⟩
      intro hi
      apply hψ0
      rw [← PFAux.re_add_im ψ, hr, hi]
      simp
    · exact ⟨_, hr, PFAux.reL2_real ψ, hRe⟩
  obtain ⟨η, hη0, hηr, hη⟩ := hex
  have hφex : ∃ φ : L2 n, φ ≠ 0 ∧ PFAux.IsRealL2 φ ∧ A φ = (‖A‖ : ℂ) • φ ∧
      ∀ᵐ x ∂volume, 0 ≤ (φ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
    rcases PFAux.real_eig_sign hpos hηr hη with h | h
    · exact ⟨η, hη0, hηr, hη, h⟩
    · refine ⟨-η, neg_ne_zero.mpr hη0, ?_, by rw [map_neg, hη, smul_neg], h⟩
      filter_upwards [hηr, Lp.coeFn_neg η] with x hx hx'
      rw [hx']
      simp [hx]
  obtain ⟨φ, hφ0, hφr, hφ, hφnn⟩ := hφex
  have hφsp : TeschlQM.OneParticle.IsStrictlyPositive (A φ) := hpos φ ⟨hφnn, hφ0⟩
  have ha_pos : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · exfalso
      have hA0 : A φ = 0 := by rw [hφ, ← h]; simp
      unfold TeschlQM.OneParticle.IsStrictlyPositive at hφsp; rw [hA0] at hφsp
      apply hφ0
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [hφsp, Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        with x h1 h2
      rw [h2] at h1
      exact absurd h1 (lt_irrefl _)
  have hφsp' : ∀ᵐ x ∂volume, 0 < (φ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
    unfold TeschlQM.OneParticle.IsStrictlyPositive at hφsp; rw [hφ] at hφsp
    filter_upwards [hφsp, Lp.coeFn_smul (‖A‖ : ℂ) φ] with x h1 h2
    rw [h2, Pi.smul_apply, smul_eq_mul] at h1
    have hinv : (0 : ℂ) < ((‖A‖⁻¹ : ℝ) : ℂ) := by exact_mod_cast inv_pos.mpr ha_pos
    have := mul_pos hinv h1
    rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha_pos.ne', Complex.ofReal_one,
      one_mul] at this
  have hspan : Module.End.eigenspace (A : Module.End ℂ (L2 n)) (‖A‖ : ℂ) = ℂ ∙ φ := by
    apply le_antisymm
    · intro χ hχ
      rw [Module.End.mem_eigenspace_iff] at hχ
      change A χ = (‖A‖ : ℂ) • χ at hχ
      obtain ⟨h1, h2⟩ := PFAux.eig_re_im hreal hχ
      obtain ⟨t1, ht1⟩ := PFAux.real_eig_mul hpos hφr hφsp' hφ hφ0 (PFAux.reL2_real χ) h1
      obtain ⟨t2, ht2⟩ := PFAux.real_eig_mul hpos hφr hφsp' hφ hφ0 (PFAux.imL2_real χ) h2
      rw [Submodule.mem_span_singleton]
      refine ⟨(t1 : ℂ) + Complex.I * t2, ?_⟩
      rw [← PFAux.re_add_im χ, ht1, ht2, add_smul, mul_smul]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Module.End.mem_eigenspace_iff.mpr hφ
  exact ⟨by rw [hspan, finrank_span_singleton hφ0], φ, hφ, hφsp'⟩
