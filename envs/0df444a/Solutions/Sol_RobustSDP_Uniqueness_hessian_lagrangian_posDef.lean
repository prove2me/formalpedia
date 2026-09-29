-- Prove2me | solution 1 for RobustSDP.Uniqueness.hessian_lagrangian_posDef
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:23:34.278105+00:00
-- url     : https://prove2.me/submissions/ae277d58-7a4e-48c0-9e49-8e7aeb145ed4

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix


namespace RobustSDP.Uniqueness

variable {m n p q : ℕ}

lemma f_expand (D : SDPData m n p q) (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (y : (Fin m → ℝ) × ℝ) :
    c ⬝ᵥ y.1 - (Z * D.G y).trace = c ⬝ᵥ y.1 - (Z * D.F y.1).trace + y.2 * (Z * (D.L * D.Lᵀ)).trace
      + y.2⁻¹ * (Z * ((D.R y.1)ᵀ * D.R y.1)).trace := by
  simp only [SDPData.G, Matrix.mul_sub, Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul]
  ring

lemma f_contDiffOn (D : SDPData m n p q) (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    ContDiffOn ℝ 2 (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace)
      {y | 0 < y.2} := by
  simp_rw [f_expand]
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiff ℝ 2 (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.F y.1).trace) := by
    simp only [dotProduct, trace, diag, mul_apply, SDPData.F, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    fun_prop
  have h2 : ContDiff ℝ 2 (fun y : (Fin m → ℝ) × ℝ => (Z * ((D.R y.1)ᵀ * D.R y.1)).trace) := by
    simp only [trace, diag, mul_apply, SDPData.R, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, transpose_apply]
    fun_prop
  have h3 : ContDiffAt ℝ 2 (fun y : (Fin m → ℝ) × ℝ => y.2⁻¹) y := by
    apply ContDiffAt.inv (by fun_prop) (ne_of_gt hy)
  exact (h1.contDiffAt.add (contDiffAt_snd.mul contDiffAt_const)).add (h3.mul h2.contDiffAt)


lemma second_deriv (K0 K1 a b c τ s : ℝ) (hτ : 0 < τ) :
    iteratedDeriv 2 (fun t : ℝ => K0 + K1 * t + (τ + t * s)⁻¹ * (a + b * t + c * t ^ 2)) 0
      = 2 * (c * τ ^ 2 - b * s * τ + a * s ^ 2) / τ ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => τ + t * s) s t := fun t => by
    have := ((hasDerivAt_id t).mul_const s).const_add τ
    exact this.congr_deriv (by simp)
  have hP : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) (b + 2 * c * t) t := fun t => by
    have := (((hasDerivAt_id t).const_mul b).const_add a).add ((hasDerivAt_pow 2 t).const_mul c)
    exact this.congr_deriv (by simp; ring)
  have hd : ∀ t, τ + t * s ≠ 0 →
      HasDerivAt (fun t : ℝ => K0 + K1 * t + (τ + t * s)⁻¹ * (a + b * t + c * t ^ 2))
        (K1 + (-s * ((τ + t * s) ^ 2)⁻¹) * (a + b * t + c * t ^ 2)
          + (τ + t * s)⁻¹ * (b + 2 * c * t)) t := by
    intro t ht
    have h2 := (hlin t).inv ht
    have h4 := ((hasDerivAt_id t).const_mul K1).const_add K0
    have := (h4.add (h2.mul (hP t)))
    exact this.congr_deriv (by simp; ring)
  have hev : deriv (fun t : ℝ => K0 + K1 * t + (τ + t * s)⁻¹ * (a + b * t + c * t ^ 2))
      =ᶠ[nhds 0] (fun t => K1 + (-s * ((τ + t * s) ^ 2)⁻¹) * (a + b * t + c * t ^ 2)
          + (τ + t * s)⁻¹ * (b + 2 * c * t)) := by
    have hopen : IsOpen {t : ℝ | τ + t * s ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds (by simp; exact ne_of_gt hτ)] with t ht
    exact (hd t ht).deriv
  rw [hev.deriv_eq]
  have hτ0 : τ + 0 * s ≠ 0 := by simp; exact ne_of_gt hτ
  have g2 : HasDerivAt (fun t : ℝ => (τ + t * s) ^ 2) (2 * τ * s) 0 := by
    have := (hlin 0).pow 2
    exact this.congr_deriv (by simp)
  have g3 := g2.inv (by simpa using pow_ne_zero 2 hτ0)
  have g5 : HasDerivAt (fun t : ℝ => b + 2 * c * t) (2 * c) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul (2 * c)).const_add b
    exact this.congr_deriv (by simp)
  have g6 := (hlin 0).inv hτ0
  have key := ((hasDerivAt_const (0:ℝ) K1).add (((g3.const_mul (-s)).mul (hP 0)))).add (g6.mul g5)
  have key' : HasDerivAt (fun t => K1 + (-s * ((τ + t * s) ^ 2)⁻¹) * (a + b * t + c * t ^ 2)
          + (τ + t * s)⁻¹ * (b + 2 * c * t)) (2 * (c * τ ^ 2 - b * s * τ + a * s ^ 2) / τ ^ 3) 0 := by
    refine key.congr_deriv ?_
    have : τ ≠ 0 := ne_of_gt hτ
    simp only [Pi.inv_apply, zero_mul, add_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    field_simp
    ring
  exact key'.deriv


lemma line_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (y0 h : E)
    (s : Set E) (hs : IsOpen s) (hy : y0 ∈ s) (hf : ContDiffOn ℝ 2 f s) :
    iteratedFDeriv ℝ 2 f y0 ![h, h] = iteratedDeriv 2 (fun t : ℝ => f (y0 + t • h)) 0 := by
  set g : E → ℝ := fun z => f (y0 + z) with hg_def
  have e1 : iteratedFDeriv ℝ 2 f y0 = iteratedFDeriv ℝ 2 g 0 := by
    rw [hg_def, iteratedFDeriv_comp_add_left]; simp
  set ℓ : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) h with hℓ
  set s' : Set E := (fun z => y0 + z) ⁻¹' s with hs'_def
  have hs' : IsOpen s' := hs.preimage (by fun_prop)
  have h0 : (0 : E) ∈ s' := by simpa [hs'_def] using hy
  have hgc : ContDiffOn ℝ 2 g s' :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun z hz => hz)
  have hs'' : IsOpen (ℓ ⁻¹' s') := hs'.preimage ℓ.continuous
  have h0' : (0 : ℝ) ∈ ℓ ⁻¹' s' := by simpa using h0
  have key := ℓ.iteratedFDerivWithin_comp_right hgc hs'.uniqueDiffOn hs''.uniqueDiffOn
    (x := 0) (by simpa using h0) (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 2 hs'' h0', map_zero,
    iteratedFDerivWithin_of_isOpen 2 hs' h0] at key
  have hcomp : (fun t : ℝ => f (y0 + t • h)) = g ∘ ℓ := by
    funext t; simp [hg_def, hℓ]
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp, key, e1]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp [hℓ]


lemma R_add (D : SDPData m n p q) (x u : Fin m → ℝ) (t : ℝ) :
    D.R (x + t • u) = D.R x + t • ∑ i, u i • D.Rs i := by
  simp only [SDPData.R, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  abel

lemma F_add (D : SDPData m n p q) (x u : Fin m → ℝ) (t : ℝ) :
    D.F (x + t • u) = D.F x + t • ∑ i, u i • D.Fs i := by
  simp only [SDPData.F, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  abel

lemma phi_eq (D : SDPData m n p q) (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (x u : Fin m → ℝ) (τ s : ℝ) :
    (fun t : ℝ => (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace) ((x, τ) + t • (u, s)))
    = fun t => (c ⬝ᵥ x - (Z * D.F x).trace + τ * (Z * (D.L * D.Lᵀ)).trace)
        + (c ⬝ᵥ u - (Z * ∑ i, u i • D.Fs i).trace + s * (Z * (D.L * D.Lᵀ)).trace) * t
        + (τ + t * s)⁻¹ * ((Z * ((D.R x)ᵀ * D.R x)).trace
          + (Z * ((D.R x)ᵀ * ∑ i, u i • D.Rs i + (∑ i, u i • D.Rs i)ᵀ * D.R x)).trace * t
          + (Z * ((∑ i, u i • D.Rs i)ᵀ * ∑ i, u i • D.Rs i)).trace * t ^ 2) := by
  funext t
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [f_expand D c Z (x + t • u, τ + t * s)]
  simp only [R_add, F_add, dotProduct_add, dotProduct_smul, smul_eq_mul, transpose_add,
    transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, trace_add,
    trace_smul]
  ring


open scoped MatrixOrder in
lemma trace_gram (B : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin q) (Fin n) ℝ) :
    (star B * B * (Kᵀ * K)).trace = ((K * Bᴴ)ᴴ * (K * Bᴴ)).trace := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    star_eq_conjTranspose]
  rw [show B * Kᵀ * (K * Bᴴ) = (B * (Kᵀ * K)) * Bᴴ by simp only [Matrix.mul_assoc],
    trace_mul_comm (B * (Kᵀ * K)) Bᴴ]
  simp only [Matrix.mul_assoc]

lemma col_zero {a : ℕ} (M R : Matrix (Fin q) (Fin n) ℝ) (Bh : Matrix (Fin n) (Fin a) ℝ)
    (hker : LinearMap.ker (Matrix.toLin' M) = LinearMap.ker (Matrix.toLin' R))
    (h : M * Bh = 0) : R * Bh = 0 := by
  ext i j
  have hv : (fun k => Bh k j) ∈ LinearMap.ker (Matrix.toLin' M) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    funext i'
    have := congrFun (congrFun h i') j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  rw [hker, LinearMap.mem_ker, Matrix.toLin'_apply] at hv
  have := congrFun hv i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

open scoped MatrixOrder in
lemma quad_pos (D : SDPData m n p q) (h3a : D.H3a) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hZ : Z.PosSemidef) (x : Fin m → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (htr : 0 < ((D.R x)ᵀ * D.R x * Z).trace) (u : Fin m → ℝ) (s : ℝ) (hh : (u, s) ≠ 0) :
    0 < (Z * ((∑ i, u i • D.Rs i)ᵀ * ∑ i, u i • D.Rs i)).trace * τ ^ 2
      - (Z * ((D.R x)ᵀ * ∑ i, u i • D.Rs i + (∑ i, u i • D.Rs i)ᵀ * D.R x)).trace * s * τ
      + (Z * ((D.R x)ᵀ * D.R x)).trace * s ^ 2 := by
  set Rl := ∑ i, u i • D.Rs i with hRl
  set M := τ • Rl - s • D.R x with hM
  have hq : (Z * (Rlᵀ * Rl)).trace * τ ^ 2
      - (Z * ((D.R x)ᵀ * Rl + Rlᵀ * D.R x)).trace * s * τ
      + (Z * ((D.R x)ᵀ * D.R x)).trace * s ^ 2 = (Z * (Mᵀ * M)).trace := by
    simp only [hM, transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul, Matrix.mul_add, trace_add]
    ring
  rw [hq]
  obtain ⟨N, _, hN⟩ := h3a
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  rw [trace_gram]
  rcases (posSemidef_conjTranspose_mul_self (M * Bᴴ)).trace_nonneg.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  rw [eq_comm, trace_conjTranspose_mul_self_eq_zero_iff] at heq
  have hMp : M = D.pencil (-s) (τ • u - s • x) := by
    simp only [hM, hRl, SDPData.pencil, SDPData.R, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, smul_add, neg_smul]
    abel
  have hRp : D.R x = D.pencil 1 x := by simp [SDPData.pencil, SDPData.R]
  have hne : (-s ≠ 0 ∨ τ • u - s • x ≠ 0) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hs : s = 0 := by linarith
    subst hs
    simp only [zero_smul, sub_zero, smul_eq_zero, ne_of_gt hτ, false_or] at h2
    exact hh (by simp [h2])
  have hker : LinearMap.ker (Matrix.toLin' M) = LinearMap.ker (Matrix.toLin' (D.R x)) := by
    rw [hMp, hRp, hN _ _ hne, hN _ _ (Or.inl one_ne_zero)]
  have hR0 := col_zero M (D.R x) Bᴴ hker heq
  have : ((D.R x)ᵀ * D.R x * (star B * B)).trace = 0 := by
    rw [trace_mul_comm, trace_gram, hR0]; simp
  linarith


theorem hess_core (D : SDPData m n p q) (h3a : D.H3a)
    (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : 0 < τ) (htr : 0 < ((D.R x)ᵀ * D.R x * Z).trace) :
    ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2
        (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace) (x, τ) ![h, h] := by
  rintro ⟨u, s⟩ hh
  rw [line_deriv _ (x, τ) (u, s) {y | 0 < y.2} (isOpen_lt continuous_const continuous_snd) hτ
    (f_contDiffOn D c Z), phi_eq, second_deriv _ _ _ _ _ _ _ hτ]
  have := quad_pos D h3a Z hZ x τ hτ htr u s hh
  apply div_pos _ (by positivity)
  linarith

end RobustSDP.Uniqueness

open RobustSDP.Uniqueness


theorem solution {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a)
    (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : 0 < τ) (htr : 0 < ((D.R x)ᵀ * D.R x * Z).trace) :
    ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2
        (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace) (x, τ) ![h, h] := by
  exact hess_core D h3a c Z hZ x τ hτ htr
