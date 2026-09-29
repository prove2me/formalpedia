-- Prove2me | solution 1 for RegularSingular.eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/23769eb7-3f03-50ec-9c88-80a962288a87

import Mathlib
import Theorems.Thm_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_mul_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt

set_option autoImplicit false

namespace FlatSharpAux

open Polynomial

theorem exists_lt_of_forall_root_lt (q : ℂ[X]) (hq : q ≠ 0) (μ : ℝ) (h : ∀ z, q.IsRoot z → z.re < μ) :
    ∃ μ₁ : ℝ, μ₁ < μ ∧ ∀ z, q.IsRoot z → z.re < μ₁ := by
  classical
  by_cases hS : q.roots.toFinset.Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := q.roots.toFinset.exists_max_image (fun z => z.re) hS
    have hz₀r : q.IsRoot z₀ := (Polynomial.mem_roots hq).1 (Multiset.mem_toFinset.1 hz₀)
    refine ⟨(z₀.re + μ) / 2, by linarith [h z₀ hz₀r], fun z hz => ?_⟩
    have := hmax z (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq).2 hz))
    have := h z₀ hz₀r
    change z.re ≤ z₀.re at *
    linarith
  · refine ⟨μ - 1, by linarith, fun z hz => ?_⟩
    exact absurd ⟨z, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq).2 hz)⟩ hS

theorem le_exp_div {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (_ht : 0 ≤ t) : t ≤ Real.exp (κ * t) / κ := by
  rw [le_div_iff₀ hκ]
  have := Real.add_one_le_exp (κ * t)
  nlinarith

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_exp_real (N : 𝔸) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • N)) (N * NormedSpace.exp ((s : ℂ) • N)) s := by
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • N)) (N * NormedSpace.exp ((s : ℂ) • N)) (s : ℂ) :=
    hasDerivAt_exp_smul_const' N (s : ℂ)
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 s := by
    have h__af := (Complex.ofRealCLM.hasDerivAt (x := s))
    simp at h__af
    exact h__af
  have := h1.scomp s h2
  simp at this
  exact this

theorem norm_exp_mul_le_aux (N : 𝔸) : ∀ (n : ℕ) (q : ℂ[X]), q.natDegree = n → q ≠ 0 →
    ∀ μ : ℝ, (∀ z : ℂ, q.IsRoot z → z.re < μ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : 𝔸, aeval N q * a = 0 → ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • N) * a‖ ≤ C * Real.exp (μ * t) * ‖a‖ := by
  intro n
  induction n with
  | zero =>
    intro q hq hq0 μ _
    refine ⟨0, le_rfl, fun a ha t _ => ?_⟩
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hq
    have hc : q.coeff 0 ≠ 0 := fun h => hq0 (by rw [hqC, h, C_0])
    rw [hqC, aeval_C, Algebra.algebraMap_eq_smul_one, smul_one_mul] at ha
    have : a = 0 := by rw [← inv_smul_smul₀ hc a, ha, smul_zero]
    rw [this, mul_zero, norm_zero]
    positivity
  | succ n ih =>
    intro q hq hq0 μ hroot

    have hdeg : q.degree ≠ 0 := by
      rw [degree_eq_natDegree hq0, hq]; exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_root q hdeg
    set q₁ : ℂ[X] := q /ₘ (X - C z₀) with hq₁
    have hfac : (X - C z₀) * q₁ = q := mul_divByMonic_eq_iff_isRoot.2 hz₀
    have hq₁deg : q₁.natDegree = n := by
      rw [hq₁, natDegree_divByMonic _ (monic_X_sub_C z₀), hq, natDegree_X_sub_C]; rfl
    have hq₁0 : q₁ ≠ 0 := fun h => hq0 (by rw [← hfac, h, mul_zero])
    have hroot₁ : ∀ z : ℂ, q₁.IsRoot z → z.re < μ := fun z hz =>
      hroot z (by rw [← hfac]; exact root_mul_left_of_isRoot _ hz)

    obtain ⟨μ₁, hμ₁, hroot'⟩ := exists_lt_of_forall_root_lt q hq0 μ hroot
    have hz₀μ₁ : z₀.re < μ₁ := hroot' z₀ hz₀
    obtain ⟨C₁, hC₁, IH⟩ := ih q₁ hq₁deg hq₁0 μ₁ (fun z hz => hroot' z (by rw [← hfac]; exact root_mul_left_of_isRoot _ hz))

    set Λ : 𝔸 := algebraMap ℂ 𝔸 z₀ with hΛ
    set D : ℝ := ‖N - Λ‖ with hD
    have hκ : 0 < μ - μ₁ := sub_pos.2 hμ₁
    refine ⟨1 + C₁ * D / (μ - μ₁), by positivity, fun a ha t ht => ?_⟩

    set b : 𝔸 := (N - Λ) * a with hb
    have hcommq : aeval N q = aeval N q₁ * (N - Λ) := by
      rw [← hfac, mul_comm, aeval_mul, map_sub, aeval_X, aeval_C]
    have hb0 : aeval N q₁ * b = 0 := by rw [hb, ← mul_assoc, ← hcommq, ha]
    have hbn : ‖b‖ ≤ D * ‖a‖ := norm_mul_le _ _

    have hEcomm : ∀ s : ℝ, Commute (N - Λ) (NormedSpace.exp ((s : ℂ) • N)) := fun s =>
      Commute.exp_right (((Commute.refl N).smul_right (s : ℂ)).sub_left
        ((Algebra.commutes z₀ ((s : ℂ) • N))))
    let w : ℝ → 𝔸 := fun s => Complex.exp (-z₀ * s) • (NormedSpace.exp ((s : ℂ) • N) * a)
    let w' : ℝ → 𝔸 := fun s => Complex.exp (-z₀ * s) • (NormedSpace.exp ((s : ℂ) • N) * b)
    have hw : ∀ s : ℝ, HasDerivAt w (w' s) s := by
      intro s
      have hc : HasDerivAt (fun u : ℝ => Complex.exp (-z₀ * u)) (Complex.exp (-z₀ * s) * (-z₀)) s := by
        have := ((Complex.hasDerivAt_exp (-z₀ * (s : ℂ))).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).const_mul (-z₀)))
        simp only [mul_one] at this
        exact this.comp_ofReal
      have hf : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • N) * a)
          (N * NormedSpace.exp ((s : ℂ) • N) * a) s := (hasDerivAt_exp_real N s).mul_const a
      have h := hc.smul hf
      convert h using 1 <;> try rfl
      show Complex.exp (-z₀ * s) • (NormedSpace.exp ((s : ℂ) • N) * b) =
        Complex.exp (-z₀ * s) • (N * NormedSpace.exp ((s : ℂ) • N) * a) +
          (Complex.exp (-z₀ * s) * -z₀) • (NormedSpace.exp ((s : ℂ) • N) * a)
      rw [hb, ← mul_assoc, ← (hEcomm s).eq, sub_mul, sub_mul, mul_smul, smul_sub, hΛ, Algebra.algebraMap_eq_smul_one,
        smul_one_mul, smul_mul_assoc]
      simp only [neg_mul, neg_smul, smul_neg, sub_eq_add_neg]

    have hε : ∀ s ∈ Set.Ico 0 t, ‖w' s‖ ≤ 0 * ‖w s‖ + C₁ * Real.exp ((μ₁ - z₀.re) * t) * ‖b‖ := by
      intro s hs
      rw [zero_mul, zero_add]
      show ‖Complex.exp (-z₀ * s) • (NormedSpace.exp ((s : ℂ) • N) * b)‖ ≤ _
      rw [norm_smul, Complex.norm_exp]
      have h1 := IH b hb0 s hs.1
      have hre : (-z₀ * (s : ℂ)).re = -z₀.re * s := by simp [Complex.mul_re]
      rw [hre]
      calc Real.exp (-z₀.re * s) * ‖NormedSpace.exp ((s : ℂ) • N) * b‖
          ≤ Real.exp (-z₀.re * s) * (C₁ * Real.exp (μ₁ * s) * ‖b‖) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C₁ * Real.exp ((μ₁ - z₀.re) * s) * ‖b‖ := by
            rw [sub_mul, Real.exp_sub, neg_mul, Real.exp_neg]; field_simp
        _ ≤ C₁ * Real.exp ((μ₁ - z₀.re) * t) * ‖b‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hC₁
            exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2.le (sub_nonneg.2 hz₀μ₁.le))
    have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := w) (f' := w') (δ := ‖a‖) (K := 0)
      (ε := C₁ * Real.exp ((μ₁ - z₀.re) * t) * ‖b‖) (a := 0) (b := t)
      (fun s _ => (hw s).continuousAt.continuousWithinAt)
      (fun s _ => (hw s).hasDerivWithinAt)
      (by show ‖Complex.exp (-z₀ * ((0 : ℝ) : ℂ)) • (NormedSpace.exp (((0 : ℝ) : ℂ) • N) * a)‖ ≤ ‖a‖
          rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, zero_smul, NormedSpace.exp_zero, one_mul])
      hε t ⟨ht, le_rfl⟩
    rw [gronwallBound_K0, sub_zero] at hG

    have hexp_eq : NormedSpace.exp ((t : ℂ) • N) * a = Complex.exp (z₀ * t) • w t := by
      show _ = Complex.exp (z₀ * t) • (Complex.exp (-z₀ * t) • (NormedSpace.exp ((t : ℂ) • N) * a))
      rw [smul_smul, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]
    have hre2 : (z₀ * (t : ℂ)).re = z₀.re * t := by simp [Complex.mul_re]
    rw [hexp_eq, norm_smul, Complex.norm_exp, hre2]

    have hE1 : Real.exp (z₀.re * t) ≤ Real.exp (μ * t) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hz₀μ₁.trans hμ₁).le ht)
    have hE2 : Real.exp (z₀.re * t) * (t * Real.exp ((μ₁ - z₀.re) * t)) ≤ Real.exp (μ * t) / (μ - μ₁) := by
      have := le_exp_div hκ ht
      calc Real.exp (z₀.re * t) * (t * Real.exp ((μ₁ - z₀.re) * t))
          = t * Real.exp (μ₁ * t) := by
            rw [sub_mul, Real.exp_sub]; field_simp
        _ ≤ Real.exp ((μ - μ₁) * t) / (μ - μ₁) * Real.exp (μ₁ * t) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = Real.exp (μ * t) / (μ - μ₁) := by
            rw [sub_mul, Real.exp_sub]; field_simp
    calc Real.exp (z₀.re * t) * ‖w t‖
        ≤ Real.exp (z₀.re * t) * (‖a‖ + C₁ * Real.exp ((μ₁ - z₀.re) * t) * ‖b‖ * t) :=
          mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
      _ ≤ Real.exp (z₀.re * t) * (‖a‖ + C₁ * Real.exp ((μ₁ - z₀.re) * t) * (D * ‖a‖) * t) := by
          gcongr
      _ = Real.exp (z₀.re * t) * ‖a‖ +
            C₁ * D * ‖a‖ * (Real.exp (z₀.re * t) * (t * Real.exp ((μ₁ - z₀.re) * t))) := by ring
      _ ≤ Real.exp (μ * t) * ‖a‖ + C₁ * D * ‖a‖ * (Real.exp (μ * t) / (μ - μ₁)) := by
          gcongr
      _ = (1 + C₁ * D / (μ - μ₁)) * Real.exp (μ * t) * ‖a‖ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring

theorem norm_exp_smul_le (N : 𝔸) (q : ℂ[X]) (hq : q ≠ 0) (hqN : aeval N q = 0)
    (μ : ℝ) (hμ : ∀ z : ℂ, q.IsRoot z → z.re < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • N)‖ ≤ C * Real.exp (μ * t) := by
  obtain ⟨C, hC, h⟩ := norm_exp_mul_le_aux N q.natDegree q rfl hq μ hμ
  refine ⟨C * ‖(1 : 𝔸)‖, by positivity, fun t ht => ?_⟩
  have := h 1 (by rw [hqN, zero_mul]) t ht
  rw [mul_one] at this
  calc _ ≤ C * Real.exp (μ * t) * ‖(1 : 𝔸)‖ := this
    _ = C * ‖(1 : 𝔸)‖ * Real.exp (μ * t) := by ring

end FlatSharpAux

namespace FlatSharpAux

open Polynomial

section Ops

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ)

noncomputable def opOf (M : Matrix (Fin r) (Fin r) ℂ) : (Fin r → E) →L[ℂ] (Fin r → E) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj j

theorem opOf_apply (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    opOf E r M v = fun i => ∑ j, M i j • v j := by
  funext i
  simp only [opOf, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]

noncomputable def opHom : Matrix (Fin r) (Fin r) ℂ →ₐ[ℂ] ((Fin r → E) →L[ℂ] (Fin r → E)) where
  toFun := opOf E r
  map_one' := by
    ext v i
    rw [opOf_apply, ContinuousLinearMap.one_apply]
    simp [Matrix.one_apply]
  map_mul' M N := by
    ext v i
    rw [ContinuousLinearMap.mul_apply, opOf_apply, opOf_apply, opOf_apply]
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
  map_zero' := by
    ext v i
    rw [opOf_apply, ContinuousLinearMap.zero_apply]
    simp
  map_add' M N := by
    ext v i
    rw [ContinuousLinearMap.add_apply, opOf_apply, opOf_apply, opOf_apply]
    simp [add_smul, Finset.sum_add_distrib]
  commutes' c := by
    ext v i
    rw [opOf_apply, Algebra.algebraMap_eq_smul_one (A := (Fin r → E) →L[ℂ] (Fin r → E)) c,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, Pi.smul_apply]
    simp [Matrix.algebraMap_matrix_apply, ite_smul]

theorem aeval_opOf_eq_zero (M : Matrix (Fin r) (Fin r) ℂ) (q : ℂ[X]) (h : aeval M q = 0) :
    aeval (opOf E r M) q = 0 := by
  have : opOf E r M = opHom E r M := rfl
  rw [this, aeval_algHom_apply, h, map_zero]

end Ops

section Bootstrap

open Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (d : ℕ)

omit [CompleteSpace X] in
theorem norm_tail_le (A : Fin d → X →L[ℂ] X) (L : ℝ) (_hL : 0 ≤ L) (hA : ∀ k, ‖A k‖ ≤ L)
    (y : ℝ) (hy0 : 0 < y) (hy1 : y ≤ 1) (x : X) :
    ‖∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k x‖ ≤ d * L * y * ‖x‖ := by
  calc ‖∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k x‖ ≤ ∑ k : Fin d, ‖((y : ℂ) ^ ((k : ℕ) + 1)) • A k x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k : Fin d, L * y * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0, pow_succ]
        calc y ^ (k : ℕ) * y * ‖A k x‖ ≤ 1 * y * (‖A k‖ * ‖x‖) := by
              apply mul_le_mul _ (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right (pow_le_one₀ hy0.le hy1) hy0.le
          _ ≤ L * y * ‖x‖ := by
              rw [one_mul]
              have := mul_le_mul_of_nonneg_right (hA k) (mul_nonneg hy0.le (norm_nonneg x))
              linarith
    _ = d * L * y * ‖x‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem bootstrap (Mop : X →L[ℂ] X) (A : Fin d → X →L[ℂ] X) (L : ℝ) (hL : 0 ≤ L) (hA : ∀ k, ‖A k‖ ≤ L)
    (μ C : ℝ) (hC : 0 ≤ C) (hexp : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : ℂ) • Mop)‖ ≤ C * Real.exp (μ * t))
    (F F' : ℝ → X)
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = Mop (F y) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (σ B : ℝ) (hμσ : μ < σ) (hB0 : 0 ≤ B) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ (C * (d * L) * B / (σ + 1 - μ)) * y ^ (σ + 1) := by
  intro y₀ hy₀
  have hκ : 0 < σ + 1 - μ := by linarith

  let yf : ℝ → ℝ := fun t => y₀ * Real.exp (-t)
  have hyf_pos : ∀ t, 0 < yf t := fun t => mul_pos hy₀.1 (Real.exp_pos _)
  have hyf_mem : ∀ t, 0 ≤ t → yf t ∈ Set.Ioc (0 : ℝ) 1 := fun t ht =>
    ⟨hyf_pos t, le_trans (mul_le_of_le_one_right hy₀.1.le (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))) hy₀.2⟩
  have hyf_deriv : ∀ t, HasDerivAt yf (-yf t) t := fun t => by
    have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul y₀
    simpa [yf, mul_comm] using this

  let T₁ : ℝ → X → X := fun y x => ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k x
  let G : ℝ → X := fun t => F (yf t)
  let G' : ℝ → X := fun t => -(Mop (G t) + T₁ (yf t) (G t))
  have hG : ∀ t, 0 ≤ t → HasDerivAt G (G' t) t := by
    intro t ht
    have h1 := (hF _ (hyf_mem t ht)).1
    have h2 := h1.scomp t (hyf_deriv t)
    have heq : (-yf t) • F' (yf t) = G' t := by
      show (-yf t) • F' (yf t) = -(Mop (F (yf t)) + T₁ (yf t) (F (yf t)))
      rw [neg_smul, ← Complex.coe_smul, (hF _ (hyf_mem t ht)).2]
    rw [← heq]
    exact h2

  let c : ℝ → (X →L[ℂ] X) := fun t => NormedSpace.exp ((t : ℂ) • Mop)
  have hc : ∀ t, HasDerivAt c (Mop * c t) t := fun t => hasDerivAt_exp_real Mop t
  have hcomm : ∀ t, Mop * c t = c t * Mop := fun t =>
    (Commute.exp_right ((Commute.refl Mop).smul_right (t : ℂ))).eq
  let V : ℝ → X := fun t => c t (G t)
  let V' : ℝ → X := fun t => -(c t (T₁ (yf t) (G t)))
  have hV : ∀ t, 0 ≤ t → HasDerivAt V (V' t) t := by
    intro t ht
    have hcR : HasDerivAt (fun s => (c s).restrictScalars ℝ) ((Mop * c t).restrictScalars ℝ) t :=
      (ContinuousLinearMap.restrictScalarsL ℂ X X ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hc t)
    have h := hcR.clm_apply (hG t ht)
    have heq : ((Mop * c t).restrictScalars ℝ) (G t) + ((c t).restrictScalars ℝ) (G' t) = V' t := by
      show (Mop * c t) (G t) + c t (-(Mop (G t) + T₁ (yf t) (G t))) = -(c t (T₁ (yf t) (G t)))
      rw [hcomm t, ContinuousLinearMap.mul_apply, map_neg, map_add]
      abel
    rw [← heq]
    exact h

  have hFTC : ∀ T : ℝ, 0 ≤ T → ∫ t in 0..T, V' t = V T - V 0 := by
    intro T hT
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hT] at ht
      exact hV t ht.1
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
      have hGc : ContinuousOn G (Set.Icc 0 T) := fun t ht => (hG t ht.1).continuousAt.continuousWithinAt
      have hyc : Continuous yf := by fun_prop
      have hT₁ : ContinuousOn (fun t => T₁ (yf t) (G t)) (Set.Icc 0 T) := by
        apply continuousOn_finsetSum
        intro k _
        exact ((Complex.continuous_ofReal.comp hyc).pow _).continuousOn.smul
          ((A k).continuous.comp_continuousOn hGc)
      exact (hcc.continuousOn.clm_apply hT₁).neg
  have hV0 : V 0 = F y₀ := by
    show NormedSpace.exp (((0 : ℝ) : ℂ) • Mop) (F (y₀ * Real.exp (-0))) = F y₀
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, neg_zero, Real.exp_zero, mul_one,
      ContinuousLinearMap.one_apply]

  set K₀ : ℝ := C * (d * L) * B * y₀ ^ (σ + 1) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; exact mul_nonneg (by positivity) (Real.rpow_nonneg hy₀.1.le _)
  have hyf_rpow : ∀ t (e : ℝ), (yf t) ^ e = y₀ ^ e * Real.exp (-(e * t)) := fun t e => by
    show (y₀ * Real.exp (-t)) ^ e = _
    rw [Real.mul_rpow hy₀.1.le (Real.exp_pos _).le, ← Real.exp_mul, neg_mul, mul_comm t e]
  have hV'le : ∀ t, 0 ≤ t → ‖V' t‖ ≤ K₀ * Real.exp (-((σ + 1 - μ) * t)) := by
    intro t ht
    show ‖-(c t (T₁ (yf t) (G t)))‖ ≤ _
    rw [norm_neg]
    have h1 := (c t).le_opNorm (T₁ (yf t) (G t))
    have h2 := hexp t ht
    have h3 := norm_tail_le d A L hL hA (yf t) (hyf_pos t) (hyf_mem t ht).2 (G t)
    have h4 := hB _ (hyf_mem t ht)
    calc ‖c t (T₁ (yf t) (G t))‖ ≤ ‖c t‖ * ‖T₁ (yf t) (G t)‖ := h1
      _ ≤ (C * Real.exp (μ * t)) * (d * L * yf t * (B * yf t ^ σ)) := by
          apply mul_le_mul h2 _ (norm_nonneg _) (by positivity)
          exact h3.trans (mul_le_mul_of_nonneg_left h4 (by have := hyf_pos t; positivity))
      _ = K₀ * Real.exp (-((σ + 1 - μ) * t)) := by
          rw [hK₀, hyf_rpow t σ]
          show C * Real.exp (μ * t) * (d * L * (y₀ * Real.exp (-t)) * (B * (y₀ ^ σ * Real.exp (-(σ * t))))) = _
          rw [Real.rpow_add hy₀.1, Real.rpow_one]
          have : Real.exp (μ * t) * Real.exp (-t) * Real.exp (-(σ * t)) = Real.exp (-((σ + 1 - μ) * t)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [← this]; ring
  have hVT : ∀ T, 0 ≤ T → ‖V T‖ ≤ C * B * y₀ ^ σ * Real.exp (-((σ - μ) * T)) := by
    intro T hT
    calc ‖V T‖ ≤ ‖c T‖ * ‖G T‖ := (c T).le_opNorm _
      _ ≤ (C * Real.exp (μ * T)) * (B * (yf T) ^ σ) :=
          mul_le_mul (hexp T hT) (hB _ (hyf_mem T hT)) (norm_nonneg _) (by positivity)
      _ = C * B * y₀ ^ σ * Real.exp (-((σ - μ) * T)) := by
          rw [hyf_rpow T σ]
          have : Real.exp (μ * T) * Real.exp (-(σ * T)) = Real.exp (-((σ - μ) * T)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [← this]; ring

  have hint : ∀ T, 0 ≤ T → ∫ t in 0..T, K₀ * Real.exp (-((σ + 1 - μ) * t)) ≤ K₀ / (σ + 1 - μ) := by
    intro T hT
    rw [intervalIntegral.integral_const_mul]
    have : ∫ t in 0..T, Real.exp (-((σ + 1 - μ) * t)) = (1 - Real.exp (-((σ + 1 - μ) * T))) / (σ + 1 - μ) := by
      have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T) Real.exp (neg_ne_zero.2 hκ.ne')
      simp only [neg_mul] at h ⊢
      rw [h, integral_exp, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
      field_simp
      ring
    rw [this]
    calc K₀ * ((1 - Real.exp (-((σ + 1 - μ) * T))) / (σ + 1 - μ)) ≤ K₀ * (1 / (σ + 1 - μ)) := by
          apply mul_le_mul_of_nonneg_left _ hK₀0
          apply div_le_div_of_nonneg_right _ hκ.le
          linarith [Real.exp_pos (-((σ + 1 - μ) * T))]
      _ = K₀ / (σ + 1 - μ) := by ring

  have hmain : ∀ T, 0 ≤ T → ‖F y₀‖ ≤ C * B * y₀ ^ σ * Real.exp (-((σ - μ) * T)) + K₀ / (σ + 1 - μ) := by
    intro T hT
    have h1 : F y₀ = V T - ∫ t in 0..T, V' t := by rw [hFTC T hT, hV0]; abel
    have h2 : ‖∫ t in 0..T, V' t‖ ≤ ∫ t in 0..T, K₀ * Real.exp (-((σ + 1 - μ) * t)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hT
      · exact Filter.Eventually.of_forall fun t ht => hV'le t ht.1.le
      · exact (by fun_prop : Continuous fun t : ℝ => K₀ * Real.exp (-((σ + 1 - μ) * t))).intervalIntegrable _ _
    rw [h1]
    exact (norm_sub_le _ _).trans (add_le_add (hVT T hT) (h2.trans (hint T hT)))

  have hlim : Tendsto (fun T : ℝ => C * B * y₀ ^ σ * Real.exp (-((σ - μ) * T)) + K₀ / (σ + 1 - μ)) atTop
      (𝓝 (C * B * y₀ ^ σ * 0 + K₀ / (σ + 1 - μ))) := by
    refine ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop (sub_pos.2 hμσ))).const_mul _).add_const _
  rw [mul_zero, zero_add] at hlim
  have := ge_of_tendsto hlim ((Filter.eventually_ge_atTop 0).mono fun T hT => hmain T hT)
  rw [hK₀] at this
  calc ‖F y₀‖ ≤ C * (↑d * L) * B * y₀ ^ (σ + 1) / (σ + 1 - μ) := this
    _ = C * (↑d * L) * B / (σ + 1 - μ) * y₀ ^ (σ + 1) := by ring

end Bootstrap

end FlatSharpAux

namespace FlatSharpAux

open Polynomial

theorem main
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E)))
    (q : Polynomial ℂ) (hq : q ≠ 0) (hqM : Polynomial.aeval M q = 0)
    (σ : ℝ) (hσ : ∀ e : ℂ, q.IsRoot e → e.re < σ)
    (F F' : ℝ → (Fin r → E))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (B : ℝ) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, F y = 0 := by

  set L : ℝ := (∑ i, ∑ j, ‖M i j‖) + ∑ k, ‖A k‖ with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hML : ∀ i j, ‖M i j‖ ≤ L := fun i j => by
    rw [hL]
    have h1 : ‖M i j‖ ≤ ∑ j', ‖M i j'‖ := Finset.single_le_sum (fun j' _ => norm_nonneg (M i j')) (Finset.mem_univ j)
    have h2 : ∑ j', ‖M i j'‖ ≤ ∑ i', ∑ j', ‖M i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖) (fun i' _ => by positivity) (Finset.mem_univ i)
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => norm_nonneg (A k))]
  have hAL : ∀ k, ‖A k‖ ≤ L := fun k => by
    rw [hL]
    have h1 : ‖A k‖ ≤ ∑ k', ‖A k'‖ := Finset.single_le_sum (fun k' _ => norm_nonneg (A k')) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := by positivity
    linarith

  obtain ⟨μ, hμσ, hμ⟩ := exists_lt_of_forall_root_lt q hq σ hσ
  have hqMop : aeval (opOf E r M) q = 0 := aeval_opOf_eq_zero E r M q hqM
  obtain ⟨C, hC, hexp⟩ := norm_exp_smul_le (opOf E r M) q hq hqMop μ hμ

  have hF' : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = opOf E r M (F y) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y) := fun y hy =>
    ⟨(hF y hy).1, by rw [opOf_apply]; exact (hF y hy).2⟩

  have hflat : ∀ k : ℕ, ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ Bk * y ^ (σ + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨max B 0, le_max_right _ _, fun y hy => ?_⟩
      rw [Nat.cast_zero, add_zero]
      exact (hB y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.1.le σ))
    | succ k ih =>
      obtain ⟨Bk, hBk0, hBk⟩ := ih
      refine ⟨C * (d * L) * Bk / (σ + k + 1 - μ), ?_, fun y hy => ?_⟩
      · have : 0 < σ + k + 1 - μ := by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
        positivity
      · have h := bootstrap d (opOf E r M) A L hL0 hAL μ C hC hexp F F' hF' (σ + k) Bk
          (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) hBk0 hBk y hy
        rw [Nat.cast_succ, ← add_assoc]
        exact h

  obtain ⟨k, hk⟩ := exists_nat_gt ((r + d) * L - σ)
  obtain ⟨Bk, -, hBk⟩ := hflat k
  exact RegularSingular.eq_zero_of_norm_le_mul_rpow_of_mul_lt E r d M A L hML hAL (σ + k) (by linarith)
    F F' hF Bk hBk

end FlatSharpAux

theorem solution
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E)))
    (q : Polynomial ℂ) (hq : q ≠ 0) (hqM : Polynomial.aeval M q = 0)
    (σ : ℝ) (hσ : ∀ e : ℂ, q.IsRoot e → e.re < σ)
    (F F' : ℝ → (Fin r → E))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
      (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y))
    (B : ℝ) (hB : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ σ) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, F y = 0 :=
  FlatSharpAux.main E r d M A q hq hqM σ hσ F F' hF B hB

end S_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt
end P2MW
export P2MW.S_RegularSingular_eq_zero_of_norm_le_mul_rpow_of_forall_isRoot_re_lt (solution)
