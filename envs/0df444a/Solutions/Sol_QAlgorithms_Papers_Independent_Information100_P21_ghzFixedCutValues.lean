-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.ghzFixedCutValues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T13:54:34.704357+00:00
-- url     : https://prove2.me/submissions/0b7885ae-6235-494c-8721-c551cbb22564

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_ghzExactRobustness

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8f_tr_vv {I : Type*} [Fintype I] (a b : I → ℂ) :
    (Matrix.vecMulVec a (star a) * Matrix.vecMulVec b (star b)).trace =
      ((Complex.normSq (∑ k, star (a k) * b k) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.diag, map_sum, map_mul,
    Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8f_tr_psd {I : Type*} [Fintype I] {A B : Op I} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨n, w, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, x8f_tr_vv, Complex.re_sum,
    Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

lemma x8f_psd_proj {I : Type*} [Fintype I] (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

section
variable {P : Type*} [Fintype P] {d : P → ℕ}

/-- Entries of a product projector. -/
lemma x8f_pent (u : (j : P) → Vec (Fin (d j))) (a b : Config d) :
    proj (productKet u) a b = ∏ j, (u j (a j) * conj (u j (b j))) := by
  simp [proj, QAlgorithms.pureDensity, productKet, Finset.prod_mul_distrib, map_prod]

/-- Polarization over the fourth roots of unity. -/
lemma x8f_pol (α β γ δ : ℂ) :
    ∑ k : Fin 4, Complex.I ^ (k : ℕ) *
      ((α + Complex.I ^ (k : ℕ) * β) * conj (γ + Complex.I ^ (k : ℕ) * δ)) = 4 * α * conj δ := by
  simp [Fin.sum_univ_four, pow_succ, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Basis vectors. -/
def x8e (j : P) (i : Fin (d j)) : Vec (Fin (d j)) := EuclideanSpace.single i 1

/-- Polarization product vectors. -/
def x8u (t : Config d × Config d × (P → Fin 4)) : (j : P) → Vec (Fin (d j)) :=
  fun j => x8e j (t.1 j) + (Complex.I ^ (t.2.2 j : ℕ)) • x8e j (t.2.1 j)

/-- Polarization coefficients. -/
def x8c (ρ : Op (Config d)) (t : Config d × Config d × (P → Fin 4)) : ℂ :=
  ρ t.1 t.2.1 * ((1/4 : ℂ) ^ Fintype.card P) * ∏ j, Complex.I ^ (t.2.2 j : ℕ)

lemma x8f_uapp (t : Config d × Config d × (P → Fin 4)) (j : P) (i : Fin (d j)) :
    x8u t j i = (if i = t.1 j then 1 else 0) + Complex.I ^ (t.2.2 j : ℕ) * (if i = t.2.1 j then 1 else 0) := by
  simp [x8u, x8e]

lemma x8f_key (ρ : Op (Config d)) (a b x y : Config d) :
    ∑ k : P → Fin 4, x8c ρ (x, y, k) * proj (productKet (x8u (x, y, k))) a b =
      ρ x y * (if a = x ∧ b = y then 1 else 0) := by
  have h1 : ∀ k : P → Fin 4, x8c ρ (x, y, k) * proj (productKet (x8u (x, y, k))) a b =
      ρ x y * (1/4 : ℂ) ^ Fintype.card P * ∏ j, (Complex.I ^ (k j : ℕ) *
        (((if a j = x j then 1 else 0) + Complex.I ^ (k j : ℕ) * (if a j = y j then 1 else 0)) *
          conj ((if b j = x j then 1 else 0) + Complex.I ^ (k j : ℕ) * (if b j = y j then 1 else 0)))) := by
    intro k
    rw [x8f_pent, x8c, mul_assoc, ← Finset.prod_mul_distrib]
    simp only [x8f_uapp]
  simp_rw [h1, ← Finset.mul_sum]
  have h2 := Finset.prod_univ_sum (fun _ : P => (Finset.univ : Finset (Fin 4)))
    (fun j (m : Fin 4) => Complex.I ^ (m : ℕ) *
        (((if a j = x j then 1 else 0) + Complex.I ^ (m : ℕ) * (if a j = y j then 1 else 0)) *
          conj ((if b j = x j then 1 else 0) + Complex.I ^ (m : ℕ) * (if b j = y j then 1 else 0))))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp_rw [x8f_pol]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h3 : ∏ j, conj (if b j = y j then (1 : ℂ) else 0) = if b = y then 1 else 0 := by
    simp_rw [apply_ite conj, map_one, map_zero]
    rw [Finset.prod_boole]
    simp [funext_iff]
  have h4 : ∏ j, (if a j = x j then (1 : ℂ) else 0) = if a = x then 1 else 0 := by
    rw [Finset.prod_boole]
    simp [funext_iff]
  rw [h3, h4]
  have h5 : (1/4 : ℂ) ^ Fintype.card P * 4 ^ Fintype.card P = 1 := by
    rw [← mul_pow]; norm_num
  by_cases ha : a = x <;> by_cases hb : b = y <;> simp [ha, hb]

lemma x8f_decC (ρ : Op (Config d)) (a b : Config d) :
    ρ a b = ∑ t, x8c ρ t * proj (productKet (x8u t)) a b := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (f := fun p : Config d × (P → Fin 4) => _)]
  simp_rw [x8f_key]
  simp_rw [ite_and]
  simp [Finset.sum_ite_eq]

lemma x8f_dec {ρ : Op (Config d)} (hρ : ρ.IsHermitian) :
    ρ = ∑ t, (((x8c ρ t).re : ℝ) : ℂ) • proj (productKet (x8u t)) := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h1 := x8f_decC ρ a b
  have h2 := x8f_decC ρ b a
  have hab : ρ a b = conj (ρ b a) := by
    have := hρ.apply a b; rw [← this]; simp
  have hc : ∀ t, conj (x8c ρ t * proj (productKet (x8u t)) b a) =
      conj (x8c ρ t) * proj (productKet (x8u t)) a b := by
    intro t; rw [map_mul, x8f_pent, x8f_pent, map_prod]
    congr 1; refine Finset.prod_congr rfl fun j _ => ?_
    simp [mul_comm]
  have : ρ a b = (ρ a b + conj (ρ b a)) / 2 := by rw [← hab]; ring
  rw [this, h1, h2, map_sum]
  simp_rw [hc, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← add_mul, Complex.add_conj]
  push_cast; ring

/-- Unit product projectors. -/
def x8S (d : P → ℕ) : Set (Op (Config d)) :=
  {X | ∃ v : (j : P) → Vec (Fin (d j)), (∀ j, ‖v j‖=1) ∧ X=proj (productKet v)}

lemma x8f_S_tr {Q : Op (Config d)} (hQ : Q ∈ x8S d) : Q.trace = 1 := by
  obtain ⟨v, hv, rfl⟩ := hQ
  have : ‖productKet v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsw := Finset.prod_univ_sum (fun _ : P => (Finset.univ))
      (fun j (b : Fin (d j)) => ‖v j b‖ ^ 2)
    simp only [Fintype.piFinset_univ] at hsw
    simp only [productKet, norm_prod, ← Finset.prod_pow]
    rw [← hsw]
    have : ∀ j, ∑ b, ‖v j b‖ ^ 2 = 1 := fun j => by
      rw [← EuclideanSpace.norm_sq_eq, hv j, one_pow]
    simp [this]
  simp only [Matrix.trace, Matrix.diag, proj, QAlgorithms.pureDensity, Matrix.of_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, ← EuclideanSpace.norm_sq_eq, this]; simp

/-- Squared norm of a product ket, as a trace. -/
def x8n (u : (j : P) → Vec (Fin (d j))) : ℝ := ∏ j, ‖u j‖ ^ 2

lemma x8f_unit (hd : ∀ j, 0 < d j) (u : (j : P) → Vec (Fin (d j))) :
    ∃ Q ∈ x8S d, proj (productKet u) = ((x8n u : ℝ) : ℂ) • Q := by
  by_cases h0 : ∃ j, u j = 0
  · obtain ⟨j0, hj0⟩ := h0
    refine ⟨proj (productKet (fun j => x8e j ⟨0, hd j⟩)), ⟨_, fun j => by simp [x8e], rfl⟩, ?_⟩
    have hn : x8n u = 0 := by
      unfold x8n; exact Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hj0])
    have hk : productKet u = 0 := by
      ext x; simp only [productKet, PiLp.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hj0])
    rw [hn, hk]; ext a b; simp [proj, QAlgorithms.pureDensity]
  · push_neg at h0
    have hne : ∀ j, ‖u j‖ ≠ 0 := fun j => norm_ne_zero_iff.mpr (h0 j)
    refine ⟨proj (productKet (fun j => ((‖u j‖⁻¹ : ℝ) : ℂ) • u j)), ⟨_, fun j => ?_, rfl⟩, ?_⟩
    · rw [norm_smul]; simp [hne j]
    · ext a b
      rw [Matrix.smul_apply, x8f_pent, x8f_pent, smul_eq_mul, x8n]
      simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      push_cast
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      have : ((‖u j‖ : ℂ)) ≠ 0 := by exact_mod_cast hne j
      field_simp

lemma x8f_tr_proj (hd : ∀ j, 0 < d j) (u : (j : P) → Vec (Fin (d j))) :
    (proj (productKet u)).trace = ((x8n u : ℝ) : ℂ) := by
  obtain ⟨Q, hQ, h⟩ := x8f_unit hd u
  rw [h, Matrix.trace_smul, x8f_S_tr hQ, smul_eq_mul, mul_one]

lemma x8f_n_nonneg (u : (j : P) → Vec (Fin (d j))) : 0 ≤ x8n u :=
  Finset.prod_nonneg fun _ _ => by positivity

lemma x8f_mem_fs (hd : ∀ j, 0 < d j) {T : Type*} [Fintype T] (w : T → ℝ) (hw : ∀ t, 0 ≤ w t)
    (u : T → (j : P) → Vec (Fin (d j))) (h1 : ∑ t, w t * x8n (u t) = 1) :
    ∑ t, ((w t : ℝ) : ℂ) • proj (productKet (u t)) ∈ fs d := by
  choose Q hQ hM using fun t => x8f_unit hd (u t)
  have : ∑ t, ((w t : ℝ) : ℂ) • proj (productKet (u t)) = ∑ t, (w t * x8n (u t)) • Q t := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hM t, smul_smul, ← Complex.ofReal_mul]
    ext a b; simp [Complex.real_smul]
  rw [this]
  exact (convex_convexHull ℝ _).sum_mem (fun t _ => mul_nonneg (hw t) (x8f_n_nonneg _)) h1
    (fun t _ => subset_convexHull ℝ _ (hQ t))

lemma x8f_psd_comb {T : Type*} [Fintype T] (w : T → ℝ) (hw : ∀ t, 0 ≤ w t)
    (u : T → (j : P) → Vec (Fin (d j))) :
    (∑ t, ((w t : ℝ) : ℂ) • proj (productKet (u t))).PosSemidef :=
  Matrix.posSemidef_sum _ fun t _ => (x8f_psd_proj _).smul (by exact_mod_cast hw t)

lemma x8f_tr_comb (hd : ∀ j, 0 < d j) {T : Type*} [Fintype T] (w : T → ℝ)
    (u : T → (j : P) → Vec (Fin (d j))) :
    (∑ t, ((w t : ℝ) : ℂ) • proj (productKet (u t))).trace = ((∑ t, w t * x8n (u t) : ℝ) : ℂ) := by
  rw [Matrix.trace_sum]; push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.trace_smul, x8f_tr_proj hd, smul_eq_mul]

lemma x8f_feas (hd : ∀ j, 0 < d j) {ρ : Op (Config d)} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∃ s : ℝ, 0 ≤ s ∧ ∃ ω : Op (Config d), QAlgorithms.IsDensityMatrix ω ∧ ω ∈ fs d ∧
      mix ρ ω s ∈ fs d := by
  obtain ⟨r, hr⟩ : ∃ r : Config d × Config d × (P → Fin 4) → ℝ,
      ρ = ∑ t, ((r t : ℝ) : ℂ) • proj (productKet (x8u t)) := ⟨_, x8f_dec hρ.1.1⟩
  have htr : ∑ t, r t * x8n (x8u t) = 1 := by
    have h := hρ.2; rw [hr, x8f_tr_comb hd] at h; exact_mod_cast h
  set p : Config d × Config d × (P → Fin 4) → ℝ := fun t => max (r t) 0 with hp
  set q : Config d × Config d × (P → Fin 4) → ℝ := fun t => max (-r t) 0 with hq
  have hp0 : ∀ t, 0 ≤ p t := fun t => le_max_right _ _
  have hq0 : ∀ t, 0 ≤ q t := fun t => le_max_right _ _
  have hrpq : ∀ t, r t = p t - q t := by
    intro t; simp only [hp, hq]
    rcases le_total (r t) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  set S := ∑ t, q t * x8n (x8u t) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => mul_nonneg (hq0 t) (x8f_n_nonneg _)
  have hpS : ∑ t, p t * x8n (x8u t) = 1 + S := by
    rw [← htr, hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hrpq]; ring
  have hw0 : ∀ t, 0 ≤ (p t + q t) / (1 + 2 * S) := fun t =>
    div_nonneg (add_nonneg (hp0 t) (hq0 t)) (by linarith)
  have hw1 : ∑ t, (p t + q t) / (1 + 2 * S) * x8n (x8u t) = 1 := by
    have e : ∀ t, (p t + q t) / (1 + 2 * S) * x8n (x8u t) =
        (p t * x8n (x8u t) + q t * x8n (x8u t)) / (1 + 2 * S) := fun t => by ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hpS, ← hS]
    field_simp; ring
  have hv0 : ∀ t, 0 ≤ p t / (1 + S) := fun t => div_nonneg (hp0 t) (by linarith)
  have hv1 : ∑ t, p t / (1 + S) * x8n (x8u t) = 1 := by
    have e : ∀ t, p t / (1 + S) * x8n (x8u t) = p t * x8n (x8u t) / (1 + S) := fun t => by ring
    simp_rw [e]
    rw [← Finset.sum_div, hpS]
    field_simp
  refine ⟨1 + 2 * S, by linarith, ∑ t, (((p t + q t) / (1 + 2 * S) : ℝ) : ℂ) •
    proj (productKet (x8u t)), ⟨x8f_psd_comb _ hw0 _, ?_⟩, x8f_mem_fs hd _ hw0 _ hw1, ?_⟩
  · rw [x8f_tr_comb hd, hw1]; simp
  · have : mix ρ (∑ t, (((p t + q t) / (1 + 2 * S) : ℝ) : ℂ) • proj (productKet (x8u t)))
        (1 + 2 * S) = ∑ t, ((p t / (1 + S) : ℝ) : ℂ) • proj (productKet (x8u t)) := by
      rw [mix, hr, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [smul_smul, ← add_smul, smul_smul]
      congr 1
      have key : (1 + (1 + 2 * S))⁻¹ * (r t + (1 + 2 * S) * ((p t + q t) / (1 + 2 * S))) =
          p t / (1 + S) := by
        rw [hrpq]; field_simp; ring
      rw [← key]; push_cast; ring
    rw [this]
    exact x8f_mem_fs hd _ hv0 _ hv1

lemma x8f_eq (ρ ω σ Z : Op (Config d)) (t : ℝ) (h : ρ + (t : ℂ) • ω = (1 + t : ℂ) • σ) :
    (Z * ρ).trace.re + t * (Z * ω).trace.re = (1 + t) * (Z * σ).trace.re := by
  have h' := congrArg (fun X => (Z * X).trace.re) h
  have e : (1 + t : ℂ) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h'
  simpa only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Complex.add_re, Complex.re_ofReal_mul] using h'

lemma x8f_mix (ρ ω : Op (Config d)) {s : ℝ} (hs : 0 ≤ s) :
    ρ + (s : ℂ) • ω = (1 + s : ℂ) • mix ρ ω s := by
  rw [mix, smul_smul]
  have : (1 + s : ℂ) * (((1 + s)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    have : (1 + (s : ℂ)) ≠ 0 := by exact_mod_cast (show (1 + s : ℝ) ≠ 0 by linarith)
    field_simp
  rw [this, one_smul]

end

/-! ## Monotonicity of robustness under free linear maps -/

lemma x8m_mix {A B : Type*} (T : Op A →ₗ[ℂ] Op B) (ρ ω : Op A) (s : ℝ) :
    T (mix ρ ω s) = mix (T ρ) (T ω) s := by
  simp only [mix, map_smul, map_add]

lemma x8m_mono {A B : Type*} {_ : Fintype A} {_ : Fintype B} {FA : Set (Op A)} {FB : Set (Op B)}
    (std : Bool) (T : Op A →ₗ[ℂ] Op B)
    (hD : ∀ X, QAlgorithms.IsDensityMatrix X → QAlgorithms.IsDensityMatrix (T X))
    (hF : ∀ X ∈ FA, T X ∈ FB) {ρ : Op A}
    (hne : ∃ s : ℝ, 0 ≤ s ∧ ∃ ω, QAlgorithms.IsDensityMatrix ω ∧ (std = true → ω ∈ FA) ∧
      mix ρ ω s ∈ FA) :
    robust FB std (T ρ) ≤ robust FA std ρ := by
  unfold robust
  obtain ⟨s0, hs0, ω0, h0⟩ := hne
  refine csInf_le_csInf ⟨0, fun s hs => hs.1⟩ ⟨s0, hs0, ω0, h0⟩ ?_
  rintro s ⟨hs, ω, hω, hωF, hm⟩
  exact ⟨hs, T ω, hD _ hω, fun h => hF _ (hωF h), by rw [← x8m_mix]; exact hF _ hm⟩

/-- A Kraus map as a linear map. -/
def x8K {A B : Type*} [Fintype A] {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) : Op A →ₗ[ℂ] Op B where
  toFun X := ∑ j, E j * X * (E j)ᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma x8K_dens {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] {K : Type*} [Fintype K]
    (E : K → Matrix B A ℂ) (hE : ∑ j, (E j)ᴴ * E j = 1) (X : Op A)
    (hX : QAlgorithms.IsDensityMatrix X) : QAlgorithms.IsDensityMatrix (x8K E X) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hX.1.mul_mul_conjTranspose_same _, ?_⟩
  change (∑ j, E j * X * (E j)ᴴ).trace = 1
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X, ← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]
  exact hX.2

/-! ## Conjugation by rectangular matrices -/

lemma x8i_proj_eq {I : Type*} (u : Vec I) : proj u = Matrix.vecMulVec (⇑u) (star ⇑u) := by
  ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]

lemma x8i_conj {A B : Type*} [Fintype A] (M : Matrix B A ℂ) (u : Vec A) :
    M * proj u * Mᴴ = proj (WithLp.toLp 2 (M *ᵥ ⇑u)) := by
  rw [x8i_proj_eq, x8i_proj_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

lemma x8i_tr_conj {A B : Type*} [Fintype A] [Fintype B] (M : Matrix B A ℂ) (X : Op A) :
    (M * X * Mᴴ).trace = (Mᴴ * M * X).trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]

/-- Complex nonnegativity of traces of products of PSD matrices. -/
lemma x8i_tr_psd {I : Type*} [Fintype I] {A B : Op I} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨n, w, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, x8f_tr_vv]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    exact_mod_cast Complex.normSq_nonneg _

section
variable {P : Type*} [Fintype P] {d f : P → ℕ}

/-- Product of local maps applied to a product ket. -/
lemma x8i_mulVec (W : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (v : (j : P) → Vec (Fin (d j))) :
    WithLp.toLp 2 (localTensor W *ᵥ ⇑(productKet v)) =
      productKet (fun j => WithLp.toLp 2 (W j *ᵥ ⇑(v j))) := by
  ext x
  simp only [productKet, localTensor, Matrix.mulVec, dotProduct, PiLp.toLp_apply]
  rw [Finset.prod_univ_sum (fun j => (Finset.univ : Finset (Fin (d j))))
    (fun j i => W j (x j) i * v j i)]
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

lemma x8i_LhL (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1) :
    (localTensor V)ᴴ * localTensor V = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localTensor, Matrix.one_apply]
  have h1 : ∀ x : Config f, star (∏ j, V j (x j) (y j)) * ∏ j, V j (x j) (y' j) =
      ∏ j, (star (V j (x j) (y j)) * V j (x j) (y' j)) := by
    intro x; rw [star_prod, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun j => (Finset.univ : Finset (Fin (f j))))
    (fun j i => star (V j i (y j)) * V j i (y' j))]
  have h2 : ∀ j, ∑ i, star (V j i (y j)) * V j i (y' j) = if y j = y' j then 1 else 0 := by
    intro j
    have := congrFun (congrFun (hV j) (y j)) (y' j)
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp_rw [h2]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma x8i_Lh (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) :
    (localTensor V)ᴴ = localTensor (fun j => (V j)ᴴ) := by
  ext y x
  simp [localTensor, Matrix.conjTranspose_apply, star_prod]

end

lemma x8m_hull {A B : Type*} (T : Op A →ₗ[ℂ] Op B) {S : Set (Op A)} {S' : Set (Op B)}
    (h : ∀ X ∈ S, T X ∈ convexHull ℝ S') : ∀ X ∈ convexHull ℝ S, T X ∈ convexHull ℝ S' :=
  fun _ hX => convexHull_min h ((convex_convexHull ℝ S').linear_preimage (T.restrictScalars ℝ)) hX

lemma x8i_tr_proj {I : Type*} [Fintype I] (v : Vec I) : (proj v).trace = ((‖v‖^2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, proj, QAlgorithms.pureDensity, Matrix.of_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, ← EuclideanSpace.norm_sq_eq]

lemma x8i_norm {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (M : Matrix B A ℂ)
    (hM : Mᴴ * M = 1) (v : Vec A) : ‖(WithLp.toLp 2 (M *ᵥ ⇑v) : Vec B)‖ = ‖v‖ := by
  have h := congrArg Matrix.trace (x8i_conj M v)
  rw [x8i_tr_conj, hM, Matrix.one_mul, x8i_tr_proj, x8i_tr_proj] at h
  have h2 : ‖v‖ ^ 2 = ‖(WithLp.toLp 2 (M *ᵥ ⇑v) : Vec B)‖ ^ 2 := by exact_mod_cast h
  have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  exact this.symm

section
variable {P : Type*} [Fintype P] {d f : P → ℕ}

lemma x8i_fs (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (X : Op (Config d)) (hX : X ∈ fs d) :
    x8K (fun _ : Fin 1 => localTensor V) X ∈ fs f := by
  refine x8m_hull (x8K (fun _ : Fin 1 => localTensor V)) ?_ X hX
  rintro _ ⟨v, hv, rfl⟩
  apply subset_convexHull
  refine ⟨fun j => WithLp.toLp 2 (V j *ᵥ ⇑(v j)), fun j => by rw [x8i_norm _ (hV j), hv j], ?_⟩
  change ∑ _ : Fin 1, localTensor V * proj (productKet v) * (localTensor V)ᴴ = _
  rw [Fin.sum_univ_one, x8i_conj, x8i_mulVec]

lemma x8i_dens (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (X : Op (Config d)) (hX : QAlgorithms.IsDensityMatrix X) :
    QAlgorithms.IsDensityMatrix (x8K (fun _ : Fin 1 => localTensor V) X) :=
  x8K_dens _ (by rw [Fin.sum_univ_one]; exact x8i_LhL V hV) X hX

/-- Reverse channel for a local isometry. -/
def x8Psi (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (τ : Op (Config d)) :
    Op (Config f) →ₗ[ℂ] Op (Config d) where
  toFun Y := (localTensor V)ᴴ * Y * localTensor V + ((1 - localTensor V * (localTensor V)ᴴ) * Y).trace • τ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, add_smul]; abel
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply,
      smul_add, mul_smul]

lemma x8i_psi_inv (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1)
    (τ : Op (Config d)) (ρ : Op (Config d)) :
    x8Psi V τ (localTensor V * ρ * (localTensor V)ᴴ) = ρ := by
  have hL := x8i_LhL V hV
  change (localTensor V)ᴴ * (localTensor V * ρ * (localTensor V)ᴴ) * localTensor V +
    ((1 - localTensor V * (localTensor V)ᴴ) * (localTensor V * ρ * (localTensor V)ᴴ)).trace • τ = ρ
  have h1 : (localTensor V)ᴴ * (localTensor V * ρ * (localTensor V)ᴴ) * localTensor V = ρ := by
    simp only [← Matrix.mul_assoc, hL, Matrix.one_mul]
    rw [Matrix.mul_assoc, hL, Matrix.mul_one]
  have h2 : (1 - localTensor V * (localTensor V)ᴴ) * (localTensor V * ρ * (localTensor V)ᴴ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (localTensor V) (localTensor V)ᴴ (localTensor V), hL, Matrix.mul_one, sub_self]
  rw [h1, h2, Matrix.trace_zero, zero_smul, add_zero]

lemma x8i_proj_psd' {I : Type*} [Fintype I] [DecidableEq I] (Q : Op I) (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) :
    (1 - Q).PosSemidef := by
  have : 1 - Q = (1 - Q)ᴴ * (1 - Q) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQ2]; abel
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma x8i_P (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1) :
    (1 - localTensor V * (localTensor V)ᴴ).PosSemidef := by
  apply x8i_proj_psd'
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (localTensor V)ᴴ, x8i_LhL V hV, Matrix.one_mul]

lemma x8i_psi_dens (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1)
    {τ : Op (Config d)} (hτ : QAlgorithms.IsDensityMatrix τ) (Y : Op (Config f))
    (hY : QAlgorithms.IsDensityMatrix Y) : QAlgorithms.IsDensityMatrix (x8Psi V τ Y) := by
  have hc := x8i_tr_psd (x8i_P V hV) hY.1
  refine ⟨(hY.1.conjTranspose_mul_mul_same _).add (hτ.1.smul hc), ?_⟩
  change ((localTensor V)ᴴ * Y * localTensor V + ((1 - localTensor V * (localTensor V)ᴴ) * Y).trace • τ).trace = 1
  rw [Matrix.trace_add, Matrix.trace_smul, hτ.2, smul_eq_mul, mul_one, Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_sub, hY.2, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  ring

lemma x8i_psi_fs (hd : ∀ j, 0 < d j) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1) (Y : Op (Config f)) (hY : Y ∈ fs f) :
    x8Psi V (proj (productKet (fun j => x8e j ⟨0, hd j⟩))) Y ∈ fs d := by
  refine x8m_hull _ ?_ Y hY
  rintro _ ⟨w, hw, rfl⟩
  set u : (j : P) → Vec (Fin (d j)) := fun j => WithLp.toLp 2 ((V j)ᴴ *ᵥ ⇑(w j)) with hu
  set e0 : (j : P) → Vec (Fin (d j)) := fun j => x8e j ⟨0, hd j⟩ with he0
  have hconj : (localTensor V)ᴴ * proj (productKet w) * localTensor V = proj (productKet u) := by
    have := x8i_conj (localTensor V)ᴴ (productKet w)
    rw [Matrix.conjTranspose_conjTranspose] at this
    rw [this, x8i_Lh, x8i_mulVec]
  have hw1 : (proj (productKet w)).trace = 1 := x8f_S_tr ⟨w, hw, rfl⟩
  have hc : ((1 - localTensor V * (localTensor V)ᴴ) * proj (productKet w)).trace =
      ((1 - x8n u : ℝ) : ℂ) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hw1, Matrix.mul_assoc,
      Matrix.trace_mul_comm (localTensor V), hconj, x8f_tr_proj hd]
    push_cast; ring
  have hc0 : 0 ≤ 1 - x8n u := by
    have := x8i_tr_psd (x8i_P V hV) (x8f_psd_proj (productKet w))
    rw [hc] at this; exact_mod_cast this
  have hn0 : x8n e0 = 1 := by
    unfold x8n; simp [he0, x8e]
  change (localTensor V)ᴴ * proj (productKet w) * localTensor V +
    ((1 - localTensor V * (localTensor V)ᴴ) * proj (productKet w)).trace • proj (productKet e0) ∈ fs d
  rw [hconj, hc]
  have := x8f_mem_fs hd (T := Fin 2) ![1, 1 - x8n u] (by intro t; fin_cases t <;> simp [hc0])
    ![u, e0] (by simp [Fin.sum_univ_two, hn0])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.ofReal_one, one_smul] at this
  exact this

end

/-! ## Spectators -/

section
variable {P Q : Type*} [Fintype P] [Fintype Q] {d : P → ℕ} {e : Q → ℕ}

def x8σ : Config (Sum.elim d e) ≃ Config d × Config e :=
  Equiv.sumPiEquivProdPi (fun j => Fin (Sum.elim d e j))

lemma x8s_eq (X : Op (Config d)) (η : Op (Config e)) :
    spectator X η = (Matrix.kronecker X η).submatrix x8σ x8σ := by
  ext x y; rfl

lemma x8s_dens {X : Op (Config d)} {η : Op (Config e)} (hX : QAlgorithms.IsDensityMatrix X)
    (hη : QAlgorithms.IsDensityMatrix η) : QAlgorithms.IsDensityMatrix (spectator X η) := by
  rw [x8s_eq]
  refine ⟨(hX.1.kronecker hη.1).submatrix _, ?_⟩
  have : ((Matrix.kronecker X η).submatrix x8σ x8σ).trace = (Matrix.kronecker X η).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Equiv.sum_comp x8σ (fun i => Matrix.kronecker X η i i)
  rw [this, Matrix.kronecker, Matrix.trace_kronecker, hX.2, hη.2, one_mul]

def x8T1 (η : Op (Config e)) : Op (Config d) →ₗ[ℂ] Op (Config (Sum.elim d e)) where
  toFun X := spectator X η
  map_add' X Y := by ext x y; exact add_mul _ _ _
  map_smul' c X := by ext x y; exact mul_assoc _ _ _

def x8T1' (X : Op (Config d)) : Op (Config e) →ₗ[ℂ] Op (Config (Sum.elim d e)) where
  toFun η := spectator X η
  map_add' X Y := by ext x y; exact mul_add _ _ _
  map_smul' c X := by ext x y; exact mul_left_comm _ _ _


lemma x8T1_apply (η : Op (Config e)) (X : Op (Config d)) : x8T1 η X = spectator X η := rfl

def x8jv (v : (j : P) → Vec (Fin (d j))) (w : (j : Q) → Vec (Fin (e j))) :
    (j : P ⊕ Q) → Vec (Fin (Sum.elim d e j)) := fun j => Sum.rec v w j

lemma x8s_gen (v : (j : P) → Vec (Fin (d j))) (w : (j : Q) → Vec (Fin (e j))) :
    spectator (proj (productKet v)) (proj (productKet w)) = proj (productKet (x8jv v w)) := by
  ext x y
  show (productKet v (fun j => x (Sum.inl j)) * conj (productKet v (fun j => y (Sum.inl j)))) *
    (productKet w (fun j => x (Sum.inr j)) * conj (productKet w (fun j => y (Sum.inr j)))) =
    productKet (x8jv v w) x * conj (productKet (x8jv v w) y)
  simp only [productKet, Fintype.prod_sum_type, map_mul, x8jv]
  ring

lemma x8s_fs {X : Op (Config d)} {η : Op (Config e)} (hX : X ∈ fs d) (hη : η ∈ fs e) :
    spectator X η ∈ fs (Sum.elim d e) := by
  have step1 : ∀ G ∈ x8S e, ∀ X ∈ fs d, spectator X G ∈ fs (Sum.elim d e) := by
    rintro _ ⟨w, hw, rfl⟩ X hX
    refine x8m_hull (x8T1 (proj (productKet w))) ?_ X hX
    rintro _ ⟨v, hv, rfl⟩
    apply subset_convexHull
    refine ⟨x8jv v w, fun j => ?_, (x8s_gen v w)⟩
    cases j with
    | inl a => exact hv a
    | inr b => exact hw b
  exact x8m_hull (x8T1' X) (fun G hG => step1 G hG X hX) η hη

/-- Kraus operators of the partial trace over the spectator. -/
def x8B (z : Config e) : Matrix (Config d) (Config (Sum.elim d e)) ℂ :=
  fun x y => if y = x8σ.symm (x, z) then 1 else 0

lemma x8T2_apply (Y : Op (Config (Sum.elim d e))) (x x' : Config d) :
    x8K (x8B (d := d) (e := e)) Y x x' = ∑ z, Y (x8σ.symm (x, z)) (x8σ.symm (x', z)) := by
  simp only [x8K, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [Matrix.mul_apply, x8B, Matrix.conjTranspose_apply, ite_mul, Finset.sum_ite_eq']

lemma x8T2_dens (Y : Op (Config (Sum.elim d e))) (hY : QAlgorithms.IsDensityMatrix Y) :
    QAlgorithms.IsDensityMatrix (x8K (x8B (d := d) (e := e)) Y) := by
  refine x8K_dens _ ?_ Y hY
  ext y y'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, x8B, Matrix.one_apply]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  have h : ∀ (z : Config e) (x : Config d),
      (if y = x8σ.symm (x, z) then (if y' = x8σ.symm (x, z) then (1:ℂ) else 0) else 0) =
        if x8σ y = (x, z) then (if y = y' then 1 else 0) else 0 := by
    intro z x
    by_cases h1 : x8σ y = (x, z)
    · have : y = x8σ.symm (x, z) := by rw [← h1]; simp
      rw [if_pos this, if_pos h1]
      by_cases h2 : y = y'
      · rw [if_pos (h2 ▸ this), if_pos h2]
      · rw [if_neg h2, if_neg (fun h => h2 (this.trans h.symm))]
    · have : ¬ y = x8σ.symm (x, z) := fun h => h1 (by rw [h]; simp)
      rw [if_neg this, if_neg h1]
  simp_rw [h]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  simp

lemma x8T2_spec (ρ : Op (Config d)) {η : Op (Config e)} (hη : η.trace = 1) :
    x8K (x8B (d := d) (e := e)) (spectator ρ η) = ρ := by
  ext x x'
  rw [x8T2_apply]
  have : ∀ z, spectator ρ η (x8σ.symm (x, z)) (x8σ.symm (x', z)) = ρ x x' * η z z := fun z => rfl
  simp_rw [this, ← Finset.mul_sum]
  have h2 : ∑ z, η z z = 1 := hη
  rw [h2, mul_one]

lemma x8T2_fs {Y : Op (Config (Sum.elim d e))} (hY : Y ∈ fs (Sum.elim d e)) :
    x8K (x8B (d := d) (e := e)) Y ∈ fs d := by
  refine x8m_hull _ ?_ Y hY
  rintro _ ⟨u, hu, rfl⟩
  apply subset_convexHull
  refine ⟨fun a => u (Sum.inl a), fun a => hu (Sum.inl a), ?_⟩
  ext x x'
  rw [x8T2_apply]
  have hpk : ∀ (x : Config d) (z : Config e), productKet u (x8σ.symm (x, z)) =
      (∏ a, u (Sum.inl a) (x a)) * ∏ b, u (Sum.inr b) (z b) := by
    intro x z
    simp only [productKet, PiLp.toLp_apply, Fintype.prod_sum_type]
    rfl
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, hpk, map_mul]
  have h1 : ∀ b : Q, ∑ i, u (Sum.inr b) i * conj (u (Sum.inr b) i) = 1 := by
    intro b
    have := x8i_tr_proj (u (Sum.inr b))
    rw [hu] at this
    calc _ = (proj (u (Sum.inr b))).trace := rfl
      _ = 1 := by rw [this]; norm_num
  have hz : ∑ z : Config e, (∏ b, u (Sum.inr b) (z b)) * conj (∏ b, u (Sum.inr b) (z b)) = 1 := by
    have := Finset.prod_univ_sum (fun b : Q => (Finset.univ : Finset (Fin (e b))))
      (fun b i => (u (Sum.inr b) i * conj (u (Sum.inr b) i) : ℂ))
    rw [Fintype.piFinset_univ] at this
    simp only [map_prod, ← Finset.prod_mul_distrib]
    rw [← this]
    exact Finset.prod_eq_one fun b _ => h1 b
  have e1 : ∀ z : Config e, ((∏ a, u (Sum.inl a) (x a)) * ∏ b, u (Sum.inr b) (z b)) *
      (conj (∏ a, u (Sum.inl a) (x' a)) * conj (∏ b, u (Sum.inr b) (z b))) =
      ((∏ a, u (Sum.inl a) (x a)) * conj (∏ a, u (Sum.inl a) (x' a))) *
        ((∏ b, u (Sum.inr b) (z b)) * conj (∏ b, u (Sum.inr b) (z b))) := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => e1 z), ← Finset.mul_sum, hz, mul_one]
  rfl

end

section
variable {P : Type*} [Fintype P]

lemma x8m_fs_dens {d : P → ℕ} {X : Op (Config d)} (hX : X ∈ fs d) : QAlgorithms.IsDensityMatrix X := by
  have hsub : fs d ⊆ {X | QAlgorithms.IsDensityMatrix X} := by
    refine convexHull_min ?_ ?_
    · rintro X ⟨v, hv, rfl⟩
      exact ⟨x8f_psd_proj _, x8f_S_tr ⟨v, hv, rfl⟩⟩
    · intro X hX Y hY a b ha hb hab
      refine ⟨(hX.1.smul (by exact_mod_cast ha)).add (hY.1.smul (by exact_mod_cast hb)), ?_⟩
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2]
      simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.ofReal_one]
      exact_mod_cast hab
  exact hsub hX

lemma x8rob_inst {A : Type*} (i1 i2 : Fintype A) (F : Set (Op A)) (std : Bool) (X : Op A) :
    @robust A i1 F std X = @robust A i2 F std X := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

lemma x8dens_inst {A : Type*} (i1 i2 : Fintype A) (X : Op A)
    (h : @QAlgorithms.IsDensityMatrix A i1 X) : @QAlgorithms.IsDensityMatrix A i2 X := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

lemma x8m_chan {P' Q' : Type*} [Fintype P'] [Fintype Q'] {d' : P' → ℕ} {e' : Q' → ℕ}
    (hd' : ∀ j, 0 < d' j)
    (F : QAlgorithms.Superop (Config d') (Config e')) (hF : QAlgorithms.IsChannel F)
    (hFf : ∀ sigma, sigma∈fs d' → F sigma∈fs e') (X : Op (Config d'))
    (hX : QAlgorithms.IsDensityMatrix X) :
    QAlgorithms.IsDensityMatrix (F X) ∧ ∀ standard : Bool, fsR e' standard (F X) ≤ fsR d' standard X := by
  obtain ⟨m, E, hE, hFE⟩ := hF
  have hT : ∀ Y, F Y = x8K E Y := fun Y => hFE Y
  have hD : ∀ Y, QAlgorithms.IsDensityMatrix Y → QAlgorithms.IsDensityMatrix (x8K E Y) :=
    fun Y hY => x8K_dens E hE Y hY
  refine ⟨by rw [hT]; exact hD X hX, fun std => ?_⟩
  obtain ⟨s, hs, ω, hω, hωF, hm⟩ := x8f_feas hd' hX
  rw [hT]
  exact x8m_mono std (x8K E) hD (fun Y hY => by rw [← hT]; exact hFf Y hY)
    ⟨s, hs, ω, hω, fun _ => hωF, hm⟩

lemma x8i_conj_pk {d f : P → ℕ} (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ)
    (g : Vec (Config d)) :
    proj (WithLp.toLp 2 (localTensor V *ᵥ ⇑g) : Vec (Config f)) =
      x8K (fun _ : Fin 1 => localTensor V) (proj g) := by
  simp only [x8K, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_one]
  rw [x8i_conj]

/-- Local isometry invariance of full-separability robustness. -/
lemma x8_iso (d : P → ℕ) (hd : ∀ j,0<d j) (rho : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho)
    (f : P → ℕ) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ)
    (hf0 : ∀ j,0<f j) (hV : ∀ j,(V j)ᴴ*V j=1) (std : Bool) :
    fsR f std (localTensor V*rho*(localTensor V)ᴴ)=fsR d std rho := by
  have hLK : localTensor V * rho * (localTensor V)ᴴ = x8K (fun _ : Fin 1 => localTensor V) rho := by
    simp [x8K]
  set e0 : (j : P) → Vec (Fin (d j)) := fun j => x8e j ⟨0, hd j⟩ with he0
  have hτ : QAlgorithms.IsDensityMatrix (proj (productKet e0)) :=
    ⟨x8f_psd_proj _, x8f_S_tr ⟨e0, fun j => by simp [he0, x8e], rfl⟩⟩
  rw [hLK]
  apply le_antisymm
  · obtain ⟨s, hs, ω, hω, hωF, hm⟩ := x8f_feas hd hr
    exact x8m_mono std _ (x8i_dens V hV) (x8i_fs V hV) ⟨s, hs, ω, hω, fun _ => hωF, hm⟩
  · obtain ⟨s, hs, ω, hω, hωF, hm⟩ := x8f_feas hf0 (x8i_dens V hV rho hr)
    have := x8m_mono std (x8Psi V (proj (productKet e0))) (x8i_psi_dens V hV hτ)
      (x8i_psi_fs hd V hV) ⟨s, hs, ω, hω, fun _ => hωF, hm⟩
    rw [← hLK, x8i_psi_inv V hV] at this
    rw [hLK] at this
    exact this


lemma x8_iso' (d : P → ℕ) (hd : ∀ j,0<d j) (g : Vec (Config d)) (hr : QAlgorithms.IsDensityMatrix (proj g))
    (f : P → ℕ) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ)
    (hf0 : ∀ j,0<f j) (hV : ∀ j,(V j)ᴴ*V j=1) (std : Bool) :
    QAlgorithms.IsDensityMatrix (proj (WithLp.toLp 2 (localTensor V *ᵥ ⇑g) : Vec (Config f))) ∧
    fsR f std (proj (WithLp.toLp 2 (localTensor V *ᵥ ⇑g) : Vec (Config f))) = fsR d std (proj g) := by
  rw [x8i_conj_pk]
  refine ⟨x8i_dens V hV _ hr, ?_⟩
  have := x8_iso d hd (proj g) hr f V hf0 hV std
  simp only [x8K, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_one]
  exact this

end

/-! ## GHZ helpers (from ghzExactRobustness development) -/

lemma x8r_ket (n : ℕ) (b : Bool) (x : Fin n → Fin 2) :
    constantKet n b x = if x = (fun _ => if b then 1 else 0) then 1 else 0 := by
  simp [constantKet, QAlgorithms.ket, PiLp.single_apply]

lemma x8r_conj (n : ℕ) (b : Bool) (x : Fin n → Fin 2) :
    conj (constantKet n b x) = constantKet n b x := by
  rw [x8r_ket]; split_ifs <;> simp

lemma x8r_ne (n : ℕ) (hn : 1 ≤ n) : (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
  intro h; have := congrFun h ⟨0, hn⟩; simp at this


/-- GHZ density as a combination of `ghzE` and `ghzC`. -/
lemma x8r_ghz (n : ℕ) (b : Bool) :
    ghz n b = ((1/2 : ℝ) : ℂ) • (ghzE n + (if b then 1 else (-1 : ℂ)) • ghzC n) := by
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * conj ((Real.sqrt 2)⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast; ring
  ext x y
  simp only [ghz, ghzKet, proj, QAlgorithms.pureDensity, Matrix.of_apply, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul, map_mul, map_add, Matrix.smul_apply, Matrix.add_apply,
    ghzE, ghzC, x8r_conj]
  cases b
  · simp only [Bool.false_eq_true, if_false, map_neg, map_one]
    linear_combination (constantKet n false x - constantKet n true x) *
      (constantKet n false y - constantKet n true y) * hs
  · simp only [if_true, map_one]
    linear_combination (constantKet n false x + constantKet n true x) *
      (constantKet n false y + constantKet n true y) * hs

lemma x8r_trE (n : ℕ) (hn : 1 ≤ n) : (ghzE n).trace = 2 := by
  have h := x8r_ne n hn
  simp only [ghzE, proj, QAlgorithms.pureDensity, Matrix.trace, Matrix.diag, Matrix.add_apply,
    Matrix.of_apply, x8r_ket]
  simp [Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  norm_num

lemma x8r_trC (n : ℕ) (hn : 1 ≤ n) : (ghzC n).trace = 0 := by
  have h := x8r_ne n hn
  simp only [ghzC, Matrix.trace, Matrix.diag, x8r_ket]
  simp [Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq', h, Ne.symm h]

lemma x8r_psd_proj {I : Type*} [Fintype I] (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma x8r_ghz_density (n : ℕ) (hn : 1 ≤ n) (b : Bool) : QAlgorithms.IsDensityMatrix (ghz n b) := by
  refine ⟨x8r_psd_proj _, ?_⟩
  rw [x8r_ghz, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, x8r_trE n hn,
    x8r_trC n hn]
  norm_num

/-! ## Embedded GHZ -/

lemma x8g_emb (n : ℕ) (hn : 2 ≤ n) (d : Fin n → ℕ) (hd2 : ∀ j, 2 ≤ d j)
    (V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1) :
    QAlgorithms.IsDensityMatrix (proj (WithLp.toLp 2 ((localTensor V).mulVec (fun x => ghzKet n true x)) : Vec (Config d))) ∧
    fsR d false (proj (WithLp.toLp 2 ((localTensor V).mulVec (fun x => ghzKet n true x)) : Vec (Config d))) = 1 ∧
    fsR d true (proj (WithLp.toLp 2 ((localTensor V).mulVec (fun x => ghzKet n true x)) : Vec (Config d))) = (2:ℝ)^(n-2) := by
  have hgd : QAlgorithms.IsDensityMatrix (ghz n true) := x8r_ghz_density n (by omega) true
  have hd0 : ∀ j, 0 < d j := fun j => by have := hd2 j; omega
  have h2 : ∀ j : Fin n, 0 < (fun _ : Fin n => 2) j := fun _ => by norm_num
  obtain ⟨hR1, hR2⟩ := ghzExactRobustness n hn
  obtain ⟨hA, hB⟩ := x8_iso' (fun _ : Fin n => 2) h2 (ghzKet n true) (x8dens_inst _ _ _ hgd) d V hd0 hV false
  obtain ⟨-, hC⟩ := x8_iso' (fun _ : Fin n => 2) h2 (ghzKet n true) (x8dens_inst _ _ _ hgd) d V hd0 hV true
  have hmv : ∀ (i1 i2 : Fintype (Config (fun _ : Fin n => 2))),
      @Matrix.mulVec _ _ ℂ _ i1 (localTensor V) (⇑(ghzKet n true)) =
        @Matrix.mulVec _ _ ℂ _ i2 (localTensor V) (⇑(ghzKet n true)) := by
    intro i1 i2
    obtain rfl : i1 = i2 := Subsingleton.elim _ _
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hmv _ inferInstance] at hA
    exact x8dens_inst _ _ _ hA
  · rw [hmv _ inferInstance] at hB
    exact hB.trans hR1
  · rw [hmv _ inferInstance] at hC
    exact hC.trans hR2

/-! ## Bipartite separable cone (from randomReplacementThreshold) -/

section
variable {I J : Type*} [Fintype I] [Fintype J]
open QAlgorithms.Entanglement

lemma x8h_psd_proj (v : Vec I) : (proj v).PosSemidef := by
  have : proj v = Matrix.vecMulVec (⇑v) (star ⇑v) := by
    ext x y; simp [proj, QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma x8h_tr_proj (v : Vec I) : (proj v).trace = ((‖v‖^2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, proj, QAlgorithms.pureDensity, Matrix.of_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, ← EuclideanSpace.norm_sq_eq]

lemma x8h_dens_proj {v : Vec I} (hv : ‖v‖ = 1) : QAlgorithms.IsDensityMatrix (proj v) :=
  ⟨x8h_psd_proj v, by rw [x8h_tr_proj, hv]; simp⟩

lemma x8h_proj_norm (u : Vec I) (hu : u ≠ 0) :
    ‖((‖u‖⁻¹ : ℝ) : ℂ) • u‖ = 1 ∧ proj u = ((‖u‖^2 : ℝ) : ℂ) • proj (((‖u‖⁻¹ : ℝ) : ℂ) • u) := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨by rw [norm_smul]; simp [hn], ?_⟩
  ext a b
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply,
    smul_eq_mul, map_mul, Complex.conj_ofReal]
  have : ((‖u‖ : ℂ)) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

lemma x8sp_zero : IsSeparablePositive (0 : Op (I × J)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · simp

lemma x8sp_add {X Y : Op (I × J)} (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) :
    IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hAB1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hAB2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [hw1]
    · simp [hw2]
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [hAB1]
    · simp [hAB2]
  · rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

lemma x8sp_smul {X : Op (I × J)} {c : ℝ} (hc : 0 ≤ c) (hX : IsSeparablePositive X) :
    IsSeparablePositive ((c : ℂ) • X) := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := hX
  refine ⟨q, fun j => c * w j, A, B, fun j => mul_nonneg hc (hw j), hAB, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]; push_cast; rfl

lemma x8sp_kron {A : Op I} {B : Op J} (hA : QAlgorithms.IsDensityMatrix A)
    (hB : QAlgorithms.IsDensityMatrix B) : IsSeparablePositive (Matrix.kronecker A B) := by
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => B, fun _ => zero_le_one, fun _ => ⟨hA, hB⟩, ?_⟩
  simp

lemma x8sp_sum {T : Type*} [Fintype T] (f : T → Op (I × J)) (h : ∀ t, IsSeparablePositive (f t)) :
    IsSeparablePositive (∑ t, f t) :=
  Finset.sum_induction _ _ (fun _ _ => x8sp_add) x8sp_zero (fun t _ => h t)

lemma x8sp_proj (u : Vec I) (v : Vec J) :
    IsSeparablePositive (Matrix.kronecker (proj u) (proj v)) := by
  by_cases hu : u = 0
  · rw [hu]; convert (x8sp_zero (I := I) (J := J)) using 1
    ext a b; simp [proj, QAlgorithms.pureDensity, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases hv : v = 0
  · rw [hv]; convert (x8sp_zero (I := I) (J := J)) using 1
    ext a b; simp [proj, QAlgorithms.pureDensity, Matrix.kronecker, Matrix.kroneckerMap_apply]
  obtain ⟨hu1, hu2⟩ := x8h_proj_norm u hu
  obtain ⟨hv1, hv2⟩ := x8h_proj_norm v hv
  rw [hu2, hv2, Matrix.kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← Complex.ofReal_mul]
  exact x8sp_smul (by positivity) (x8sp_kron (x8h_dens_proj hu1) (x8h_dens_proj hv1))

end

/-! ## The cut state -/

section
variable {A B : Type*} [Fintype A] [Fintype B]
open QAlgorithms.Entanglement

def x8ind {X : Type*} (a x : X) : ℂ := if x = a then 1 else 0

lemma x8ind_conj {X : Type*} (a x : X) : conj (x8ind a x) = x8ind a x := by
  unfold x8ind; split_ifs <;> simp

def x8ψ (a0 a1 : A) (b0 b1 : B) : Vec (A × B) :=
  WithLp.toLp 2 fun x => ((Real.sqrt 2)⁻¹ : ℂ) * (x8ind a0 x.1 * x8ind b0 x.2 + x8ind a1 x.1 * x8ind b1 x.2)

def x8ω (a0 a1 : A) (b0 b1 : B) : Op (A × B) :=
  Matrix.of fun x y => ((1/2 : ℝ) : ℂ) *
    (x8ind a0 x.1 * x8ind b1 x.2 * x8ind a0 y.1 * x8ind b1 y.2 +
      x8ind a1 x.1 * x8ind b0 x.2 * x8ind a1 y.1 * x8ind b0 y.2)

def x8cu (a0 a1 : A) (k : Fin 4) : Vec A :=
  WithLp.toLp 2 fun x => x8ind a0 x + Complex.I ^ (k : ℕ) * x8ind a1 x
def x8cv (b0 b1 : B) (k : Fin 4) : Vec B :=
  WithLp.toLp 2 fun y => x8ind b0 y + conj (Complex.I ^ (k : ℕ)) * x8ind b1 y

lemma x8c_hs : ((Real.sqrt 2)⁻¹ : ℂ) * conj ((Real.sqrt 2)⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

lemma x8c_dec (a0 a1 : A) (b0 b1 : B) :
    mix (proj (x8ψ a0 a1 b0 b1)) (x8ω a0 a1 b0 b1) 1 =
      ∑ k : Fin 4, ((1/16 : ℝ) : ℂ) • Matrix.kronecker (proj (x8cu a0 a1 k)) (proj (x8cv b0 b1 k)) := by
  have hr : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hs' : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  ext x y
  simp only [mix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, proj, QAlgorithms.pureDensity, Matrix.of_apply,
    x8ψ, x8ω, x8cu, x8cv, map_mul, map_add, x8ind_conj, Complex.conj_conj, Fin.sum_univ_four, hr]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3, pow_zero, pow_one, map_one,
    Complex.I_sq, hI3, map_neg, Complex.conj_I]
  push_cast
  ring_nf
  simp only [Complex.I_sq, hI3, hI4]
  ring_nf
  linear_combination (1/2 : ℂ) * (x8ind a0 x.1 * x8ind b0 x.2 + x8ind a1 x.1 * x8ind b1 x.2) *
    (x8ind a0 y.1 * x8ind b0 y.2 + x8ind a1 y.1 * x8ind b1 y.2) * hs'

lemma x8ind_sum {X : Type*} [Fintype X] (a : X) (f : X → ℂ) : ∑ x, x8ind a x * f x = f a := by
  simp [x8ind, ite_mul, Finset.sum_ite_eq']

/-- The overlap of ψ with a product vector. -/
lemma x8c_ov (a0 a1 : A) (b0 b1 : B) (p : A → ℂ) (q : B → ℂ) :
    ∑ x : A × B, conj (x8ψ a0 a1 b0 b1 x) * (p x.1 * q x.2) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (p a0 * q b0 + p a1 * q b1) := by
  have hr : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal]
  have h : ∀ x : A × B, conj (x8ψ a0 a1 b0 b1 x) * (p x.1 * q x.2) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (x8ind a0 x.1 * (x8ind b0 x.2 * (p x.1 * q x.2)) +
        x8ind a1 x.1 * (x8ind b1 x.2 * (p x.1 * q x.2))) := by
    intro x
    simp only [x8ψ, map_mul, map_add, x8ind_conj, hr]
    ring
  simp_rw [h, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [x8ind_sum b0 (fun y => _ * q y), x8ind_sum b1 (fun y => _ * q y)]
  rw [x8ind_sum a0 (fun x => p x * q b0), x8ind_sum a1 (fun x => p x * q b1)]

lemma x8c_cs (u0 u1 v0 v1 : ℂ) :
    Complex.normSq (u0 * v0 + u1 * v1) ≤
      (Complex.normSq u0 + Complex.normSq u1) * (Complex.normSq v0 + Complex.normSq v1) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h1 : ‖u0 * v0 + u1 * v1‖ ≤ ‖u0‖ * ‖v0‖ + ‖u1‖ * ‖v1‖ := by
    calc ‖u0 * v0 + u1 * v1‖ ≤ ‖u0 * v0‖ + ‖u1 * v1‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have h0 : 0 ≤ ‖u0 * v0 + u1 * v1‖ := norm_nonneg _
  have := sq_nonneg (‖u0‖ * ‖v1‖ - ‖u1‖ * ‖v0‖)
  have h2 : ‖u0 * v0 + u1 * v1‖ ^ 2 ≤ (‖u0‖ * ‖v0‖ + ‖u1‖ * ‖v1‖) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  nlinarith [norm_nonneg u0, norm_nonneg u1, norm_nonneg v0, norm_nonneg v1]

lemma x8c_pair {X : Type*} [Fintype X] {a0 a1 : X} (h : a0 ≠ a1) (p : X → ℂ) :
    Complex.normSq (p a0) + Complex.normSq (p a1) ≤ ∑ a, Complex.normSq (p a) := by
  rw [← Finset.sum_pair (f := fun a => Complex.normSq (p a)) h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Complex.normSq_nonneg _)

lemma x8c_trψ (a0 a1 : A) (b0 b1 : B) (M : Op (A × B)) :
    (M * proj (x8ψ a0 a1 b0 b1)).trace = (1/2 : ℂ) * (M (a0, b0) (a0, b0) + M (a0, b0) (a1, b1) +
      M (a1, b1) (a0, b0) + M (a1, b1) (a1, b1)) := by
  have hs' : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hr : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hψ : ∀ y : A × B, x8ψ a0 a1 b0 b1 y =
      ((Real.sqrt 2)⁻¹ : ℂ) * (x8ind (a0, b0) y + x8ind (a1, b1) y) := by
    intro y
    simp only [x8ψ, x8ind, PiLp.toLp_apply, Prod.ext_iff]
    congr 1
    split_ifs <;> simp_all
  have hψc : ∀ y : A × B, conj (x8ψ a0 a1 b0 b1 y) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (x8ind (a0, b0) y + x8ind (a1, b1) y) := by
    intro y; rw [hψ, map_mul, hr, map_add, x8ind_conj, x8ind_conj]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, proj, QAlgorithms.pureDensity,
    Matrix.of_apply]
  calc ∑ x, ∑ y, M x y * ((x8ψ a0 a1 b0 b1) y * conj ((x8ψ a0 a1 b0 b1) x))
      = ∑ x, ∑ y, (1/2 : ℂ) * (x8ind (a0, b0) x * (x8ind (a0, b0) y * M x y) +
          x8ind (a0, b0) x * (x8ind (a1, b1) y * M x y) +
          x8ind (a1, b1) x * (x8ind (a0, b0) y * M x y) + x8ind (a1, b1) x * (x8ind (a1, b1) y * M x y)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hψ, hψ, map_mul, hr, map_add, x8ind_conj, x8ind_conj, ← hs']; ring
    _ = _ := by simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, x8ind_sum]

lemma x8c_trvv {X : Type*} [Fintype X] {m : ℕ} (p : Fin m → X → ℂ) :
    (∑ i, Matrix.vecMulVec (p i) (star (p i))).trace.re = ∑ i, ∑ a, Complex.normSq (p i a) := by
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]

lemma x8c_wit {a0 a1 : A} {b0 b1 : B} (ha : a0 ≠ a1) (hb : b0 ≠ b1) {P : Op A} {Q : Op B}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    ((Matrix.kronecker P Q) * proj (x8ψ a0 a1 b0 b1)).trace.re ≤ (1/2) * P.trace.re * Q.trace.re := by
  obtain ⟨m, p, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  obtain ⟨m', q, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hQ
  rw [x8c_trψ, x8c_trvv, x8c_trvv]
  have key : (1/2 : ℂ) * (Matrix.kronecker (∑ i, Matrix.vecMulVec (p i) (star (p i)))
      (∑ j, Matrix.vecMulVec (q j) (star (q j))) (a0, b0) (a0, b0) +
      Matrix.kronecker (∑ i, Matrix.vecMulVec (p i) (star (p i)))
      (∑ j, Matrix.vecMulVec (q j) (star (q j))) (a0, b0) (a1, b1) +
      Matrix.kronecker (∑ i, Matrix.vecMulVec (p i) (star (p i)))
      (∑ j, Matrix.vecMulVec (q j) (star (q j))) (a1, b1) (a0, b0) +
      Matrix.kronecker (∑ i, Matrix.vecMulVec (p i) (star (p i)))
      (∑ j, Matrix.vecMulVec (q j) (star (q j))) (a1, b1) (a1, b1)) =
      (((1/2 : ℝ) * ∑ i, ∑ j, Complex.normSq (p i a0 * q j b0 + p i a1 * q j b1) : ℝ) : ℂ) := by
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, RCLike.star_def]
    push_cast
    simp_rw [← Complex.mul_conj, map_add, map_mul]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, Complex.ofReal_re]
  have hcs : ∀ i j, Complex.normSq (p i a0 * q j b0 + p i a1 * q j b1) ≤
      (Complex.normSq (p i a0) + Complex.normSq (p i a1)) * (Complex.normSq (q j b0) + Complex.normSq (q j b1)) :=
    fun i j => x8c_cs _ _ _ _
  have h1 : ∑ i, ∑ j, Complex.normSq (p i a0 * q j b0 + p i a1 * q j b1) ≤
      (∑ i, ∑ a, Complex.normSq (p i a)) * (∑ j, ∑ b, Complex.normSq (q j b)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    refine (hcs i j).trans ?_
    exact mul_le_mul (x8c_pair ha (p i)) (x8c_pair hb (q j))
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  nlinarith

lemma x8c_sep_bound {a0 a1 : A} {b0 b1 : B} (ha : a0 ≠ a1) (hb : b0 ≠ b1) {σ : Op (A × B)}
    (hσ : sep σ) : (σ * proj (x8ψ a0 a1 b0 b1)).trace.re ≤ 1/2 := by
  obtain ⟨⟨q, w, A', B', hw, hAB, rfl⟩, htr⟩ := hσ
  have hw1 : ∑ j, w j = 1 := by
    rw [Matrix.trace_sum] at htr
    have : ∀ j, ((w j : ℂ) • Matrix.kronecker (A' j) (B' j)).trace = (w j : ℂ) := by
      intro j; rw [Matrix.trace_smul, Matrix.kronecker, Matrix.trace_kronecker, (hAB j).1.2,
        (hAB j).2.2]; simp
    simp_rw [this] at htr
    exact_mod_cast htr
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  calc ∑ j, (((w j : ℂ) • Matrix.kronecker (A' j) (B' j)) * proj (x8ψ a0 a1 b0 b1)).trace.re
      ≤ ∑ j, w j * (1/2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
        have := x8c_wit ha hb (hAB j).1.1 (hAB j).2.1
        rw [(hAB j).1.2, (hAB j).2.2, Complex.one_re, mul_one, mul_one] at this
        exact mul_le_mul_of_nonneg_left this (hw j)
    _ = 1/2 := by rw [← Finset.sum_mul, hw1, one_mul]

def x8e1 {X : Type*} (a : X) : Vec X := EuclideanSpace.single a 1

lemma x8e1_apply {X : Type*} (a x : X) : x8e1 a x = x8ind a x := by
  simp [x8e1, x8ind]

lemma x8c_tensor_kron {X Y : Type*} (u : Vec X) (v : Vec Y) :
    proj (tensor u v) = Matrix.kronecker (proj u) (proj v) := by
  ext x y
  simp only [proj, QAlgorithms.pureDensity, tensor, Matrix.of_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, map_mul, PiLp.toLp_apply]
  ring

lemma x8ω_eq (a0 a1 : A) (b0 b1 : B) :
    x8ω a0 a1 b0 b1 = ((1/2 : ℝ) : ℂ) • (proj (tensor (x8e1 a0) (x8e1 b1)) +
      proj (tensor (x8e1 a1) (x8e1 b0))) := by
  ext x y
  simp only [x8ω, proj, QAlgorithms.pureDensity, tensor, Matrix.of_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul, PiLp.toLp_apply, x8e1_apply, map_mul, x8ind_conj]
  ring

lemma x8ind_sq {X : Type*} (a x : X) : x8ind a x * x8ind a x = x8ind a x := by
  unfold x8ind; split_ifs <;> simp

lemma x8c_trω (a0 a1 : A) (b0 b1 : B) : (x8ω a0 a1 b0 b1).trace = 1 := by
  simp only [x8ω, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have e : ∀ (a : A) (b : B) (x : A) (y : B), x8ind a x * x8ind b y * x8ind a x * x8ind b y =
      x8ind a x * x8ind b y := by
    intro a b x y
    calc _ = (x8ind a x * x8ind a x) * (x8ind b y * x8ind b y) := by ring
      _ = _ := by rw [x8ind_sq, x8ind_sq]
  simp_rw [e, ← Finset.mul_sum]
  have h1 : ∀ (b : B), ∑ y, x8ind b y = 1 := fun b => by
    have := x8ind_sum b (fun _ => (1 : ℂ)); simpa using this
  simp_rw [h1, mul_one]
  have h2 : ∀ (a : A), ∑ x, x8ind a x = 1 := fun a => by
    have := x8ind_sum a (fun _ => (1 : ℂ)); simpa using this
  rw [h2, h2]; push_cast; ring

lemma x8c_ω_dens (a0 a1 : A) (b0 b1 : B) : QAlgorithms.IsDensityMatrix (x8ω a0 a1 b0 b1) := by
  refine ⟨?_, x8c_trω a0 a1 b0 b1⟩
  rw [x8ω_eq]
  exact ((x8f_psd_proj _).add (x8f_psd_proj _)).smul (Complex.zero_le_real.mpr (by norm_num))

lemma x8c_ω_sep (a0 a1 : A) (b0 b1 : B) :
    QAlgorithms.Entanglement.IsSeparablePositive (x8ω a0 a1 b0 b1) := by
  rw [x8ω_eq, smul_add, x8c_tensor_kron, x8c_tensor_kron]
  exact x8sp_add (x8sp_smul (by norm_num) (x8sp_proj _ _)) (x8sp_smul (by norm_num) (x8sp_proj _ _))

lemma x8ψ_p0 {a0 a1 : A} {b0 b1 : B} (ha : a0 ≠ a1) :
    x8ψ a0 a1 b0 b1 (a0, b0) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [x8ψ, x8ind, ha]
lemma x8ψ_p1 {a0 a1 : A} {b0 b1 : B} (ha : a0 ≠ a1) :
    x8ψ a0 a1 b0 b1 (a1, b1) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [x8ψ, x8ind, Ne.symm ha]

lemma x8c_val {a0 a1 : A} {b0 b1 : B} (ha : a0 ≠ a1) (hb : b0 ≠ b1) (std : Bool) :
    robust {X : Op (A × B) | sep X} std (proj (x8ψ a0 a1 b0 b1)) = 1 := by
  have hs' : ((Real.sqrt 2)⁻¹ : ℂ) * conj ((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  have hp : (a0, b0) ≠ (a1, b1) := fun h => ha (congrArg Prod.fst h)
  have htrψ : (proj (x8ψ a0 a1 b0 b1)).trace = 1 := by
    have := x8c_trψ a0 a1 b0 b1 1
    rw [Matrix.one_mul] at this
    rw [this]
    simp [Matrix.one_apply, hp, Ne.symm hp]; norm_num
  have hψψ : (proj (x8ψ a0 a1 b0 b1) * proj (x8ψ a0 a1 b0 b1)).trace.re = 1 := by
    rw [x8c_trψ]
    simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, x8ψ_p0 ha, x8ψ_p1 ha, hs']
    norm_num
  have hρ : QAlgorithms.IsDensityMatrix (proj (x8ψ a0 a1 b0 b1)) := ⟨x8f_psd_proj _, htrψ⟩
  have hmix : sep (mix (proj (x8ψ a0 a1 b0 b1)) (x8ω a0 a1 b0 b1) 1) := by
    refine ⟨?_, ?_⟩
    · rw [x8c_dec]
      exact x8sp_sum _ fun k => x8sp_smul (by norm_num) (x8sp_proj _ _)
    · rw [mix, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, htrψ, x8c_trω]
      norm_num
  unfold robust
  apply IsLeast.csInf_eq
  refine ⟨⟨zero_le_one, x8ω a0 a1 b0 b1, x8c_ω_dens a0 a1 b0 b1,
    fun _ => ⟨x8c_ω_sep a0 a1 b0 b1, x8c_trω a0 a1 b0 b1⟩, hmix⟩, ?_⟩
  rintro s ⟨hs, ω, hω, -, hm⟩
  have h1 := x8c_sep_bound ha hb hm
  have h2 : (mix (proj (x8ψ a0 a1 b0 b1)) ω s * proj (x8ψ a0 a1 b0 b1)).trace.re =
      (1 + s)⁻¹ * (1 + s * (ω * proj (x8ψ a0 a1 b0 b1)).trace.re) := by
    simp only [mix, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add,
      smul_eq_mul, Complex.re_ofReal_mul, Complex.add_re, hψψ]
  have h3 := x8f_tr_psd hω.1 (x8f_psd_proj (x8ψ a0 a1 b0 b1))
  rw [h2] at h1
  have h4 : (0:ℝ) < 1 + s := by linarith
  rw [inv_mul_le_iff₀ h4] at h1
  nlinarith

lemma x8c_cut (n : ℕ) (S : Finset (Fin n)) (hne : S.Nonempty) :
    cutGHZ n S = proj (x8ψ (A := Side (fun _ : Fin n => 2) S) (B := Side (fun _ : Fin n => 2) Sᶜ)
      (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)) := by
  unfold cutGHZ
  congr 1
  ext x
  simp only [x8ψ, x8ind, PiLp.toLp_apply]
  have e0 : ∀ {T : Finset (Fin n)} (z : Side (fun _ : Fin n => 2) T),
      (∀ j, z j = 0) ↔ z = fun _ => 0 := fun z => ⟨fun h => funext h, fun h j => by rw [h]⟩
  have e1 : ∀ {T : Finset (Fin n)} (z : Side (fun _ : Fin n => 2) T),
      (∀ j, z j = 1) ↔ z = fun _ => 1 := fun z => ⟨fun h => funext h, fun h j => by rw [h]⟩
  simp only [e0, e1]
  obtain ⟨j0, hj0⟩ := hne
  have hne01 : ¬ ((fun _ => (0 : Fin 2)) : Side (fun _ : Fin n => 2) S) = (fun _ => 1) := by
    intro h; have := congrFun h ⟨j0, hj0⟩; simp at this
  by_cases h0 : x.1 = (fun _ => 0) <;> by_cases h1 : x.2 = (fun _ => 0) <;>
    by_cases h2 : x.1 = (fun _ => 1) <;> by_cases h3 : x.2 = (fun _ => 1) <;>
    simp_all

end

/-- A rank-two criterion: two orthonormal outer products. -/
lemma x8sum_inst {X : Type*} (i1 i2 : Fintype X) (f : X → ℂ) :
    @Finset.sum X ℂ _ (@Finset.univ X i1) f = @Finset.sum X ℂ _ (@Finset.univ X i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

lemma x8c_rank2 {X Y : Type*} {_ : Fintype X} {_ : Fintype Y} (α : Fin 2 → X → ℂ) (β : Fin 2 → Y → ℂ)
    (hα : ∀ k l, ∑ x, conj (α k x) * α l x = if k = l then 1 else 0)
    (hβ : ∀ k l, ∑ y, conj (β k y) * β l y = if k = l then 1 else 0) {c : ℂ} (hc : c ≠ 0)
    (C : Matrix X Y ℂ) (hC : ∀ x y, C x y = c * (α 0 x * β 0 y + α 1 x * β 1 y)) : C.rank = 2 := by
  apply le_antisymm
  · have hfac : C = (Matrix.of fun x k => c * α k x) * (Matrix.of fun k y => β k y) := by
      ext x y; rw [hC, Matrix.mul_apply, Fin.sum_univ_two]; simp; ring
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  · have hβ' : ∀ k l, ∑ y, β k y * conj (β l y) = if k = l then 1 else 0 := by
      intro k l
      rw [show (∑ y, β k y * conj (β l y)) = ∑ y, conj (β l y) * β k y from
        Finset.sum_congr rfl fun y _ => mul_comm _ _, hβ l k]
      by_cases h : k = l
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]
    have hmem : ∀ l, α l ∈ LinearMap.range C.mulVecLin := by
      intro l
      refine ⟨fun y => c⁻¹ * conj (β l y), ?_⟩
      ext x
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hC]
      have e : ∀ y, c * (α 0 x * β 0 y + α 1 x * β 1 y) * (c⁻¹ * conj (β l y)) =
          α 0 x * (β 0 y * conj (β l y)) + α 1 x * (β 1 y * conj (β l y)) := by
        intro y; field_simp
      simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hβ']
      fin_cases l <;> simp
    have hli : LinearIndependent ℂ α := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := congrArg (fun v => ∑ x, conj (α i x) * v x) hg
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, Finset.mul_sum] at this
      rw [Finset.sum_comm] at this
      simp_rw [show ∀ (k : Fin 2) (x : X), conj (α i x) * (g k * α k x) = g k * (conj (α i x) * α k x)
        from fun k x => by ring, ← Finset.mul_sum, hα] at this
      simpa using this
    have h2 := finrank_span_eq_card hli
    have hle : Submodule.span ℂ (Set.range α) ≤ LinearMap.range C.mulVecLin :=
      Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hmem l)
    have := Submodule.finrank_mono hle
    rw [h2] at this
    simpa [Matrix.rank] using this

lemma x8c_orth {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n)) (hT : T.Nonempty)
    (V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ) (hV : ∀ j, (V j)ᴴ * V j = 1) (k l : Fin 2) :
    ∑ x : Side d T, conj (∏ j : {j // j ∈ T}, V j (x j) k) * (∏ j : {j // j ∈ T}, V j (x j) l) =
      if k = l then 1 else 0 := by
  have h1 : ∀ x : Side d T, conj (∏ j : {j // j ∈ T}, V j (x j) k) * (∏ j : {j // j ∈ T}, V j (x j) l) =
      ∏ j : {j // j ∈ T}, (conj (V j (x j) k) * V j (x j) l) := by
    intro x; rw [map_prod, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun j : {j // j ∈ T} => (Finset.univ : Finset (Fin (d j))))
    (fun j i => conj (V j i k) * V j i l)]
  have h2 : ∀ j : {j // j ∈ T}, ∑ i, conj (V j i k) * V j i l = if k = l then 1 else 0 := by
    intro j
    have := congrFun (congrFun (hV j) k) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp_rw [h2]
  rw [Finset.prod_const, Finset.card_univ]
  have hc : 0 < Fintype.card {j // j ∈ T} := by
    rw [Fintype.card_coe]; exact hT.card_pos
  split_ifs
  · simp
  · exact zero_pow (by omega)

lemma x8c_Cform {n : ℕ} (S : Finset (Fin n)) {d : Fin n → ℕ}
    (V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ) (x : Side d S) (y : Side d Sᶜ) :
    (WithLp.toLp 2 ((localTensor V).mulVec (fun x => ghzKet n true x)) : Vec (Config d))
      (fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, by simp [hj]⟩) =
    ((Real.sqrt 2)⁻¹ : ℂ) * ((∏ j : {j // j ∈ S}, V j (x j) 0) * (∏ j : {j // j ∈ Sᶜ}, V j (y j) 0) +
      (∏ j : {j // j ∈ S}, V j (x j) 1) * (∏ j : {j // j ∈ Sᶜ}, V j (y j) 1)) := by
  set z : Config d := fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, by simp [hj]⟩ with hz
  have hsplit : ∀ c : Fin 2, ∏ j, V j (z j) c =
      (∏ j : {j // j ∈ S}, V j (x j) c) * (∏ j : {j // j ∈ Sᶜ}, V j (y j) c) := by
    intro c
    rw [← Finset.prod_mul_prod_compl S, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Sᶜ]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp only [hz, dif_pos j.2]
    · refine Finset.prod_congr rfl fun j _ => ?_
      have : (j : Fin n) ∉ S := Finset.mem_compl.mp j.2
      simp only [hz, dif_neg this]
  show (∑ w, localTensor V z w * ghzKet n true w) = _
  have hg : ∀ w : Fin n → Fin 2, ghzKet n true w =
      ((Real.sqrt 2)⁻¹ : ℂ) * (x8ind (fun _ => 0) w + x8ind (fun _ => 1) w) := by
    intro w
    simp only [ghzKet, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, if_true, one_smul, x8r_ket,
      x8ind, Bool.false_eq_true, if_false]
    congr
  simp_rw [hg, mul_add, Finset.sum_add_distrib]
  have e : ∀ c : Fin n → Fin 2, ∑ w, localTensor V z w * (((Real.sqrt 2)⁻¹ : ℂ) * x8ind c w) =
      ((Real.sqrt 2)⁻¹ : ℂ) * localTensor V z c := by
    intro c
    simp only [x8ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    simp [mul_comm]
  rw [e, e]
  simp only [localTensor]
  rw [hsplit 0, hsplit 1]

theorem x8_main (n : ℕ) (hn : 2≤n) (S : Finset (Fin n))
  (hne : S.Nonempty) (hproper : S≠Finset.univ) :
  QAlgorithms.IsDensityMatrix (cutGHZ n S) ∧ ¬sep (cutGHZ n S) ∧
  rs (cutGHZ n S)=1 ∧ rg (cutGHZ n S)=1 ∧
  (∀ (d : Fin n → ℕ), (∀ j, 2 ≤ d j) →
    ∀ V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ,
    (∀ j, (V j)ᴴ * V j = 1) →
    let psi : Vec (Config d) := WithLp.toLp 2
      ((localTensor V).mulVec (fun x => ghzKet n true x))
    let C : Matrix (Side d S) (Side d Sᶜ) ℂ := fun x y =>
      psi (fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, by simp [hj]⟩)
    QAlgorithms.IsDensityMatrix (proj psi) ∧
    fsR d false (proj psi) = 1 ∧ fsR d true (proj psi) = (2 : ℝ)^(n-2) ∧
    Matrix.rank C = 2 ∧
    (3 ≤ n → fsR d false (proj psi) < fsR d true (proj psi))) := by
  obtain ⟨j0, hj0⟩ := hne
  obtain ⟨j1, hj1⟩ : ∃ j, j ∉ S := by
    by_contra h; push_neg at h; exact hproper (Finset.eq_univ_of_forall h)
  have ha : ((fun _ => (0 : Fin 2)) : Side (fun _ : Fin n => 2) S) ≠ (fun _ => 1) := by
    intro h; have := congrFun h ⟨j0, hj0⟩; simp at this
  have hb : ((fun _ => (0 : Fin 2)) : Side (fun _ : Fin n => 2) Sᶜ) ≠ (fun _ => 1) := by
    intro h; have := congrFun h ⟨j1, by simp [hj1]⟩; simp at this
  have hcut := x8c_cut n S ⟨j0, hj0⟩
  have hR := x8c_val ha hb
  have hrs : rs (cutGHZ n S) = 1 := by rw [hcut]; exact hR true
  have hrg : rg (cutGHZ n S) = 1 := by rw [hcut]; exact hR false
  have hdens : QAlgorithms.IsDensityMatrix (cutGHZ n S) := by
    rw [hcut]
    refine ⟨x8f_psd_proj _, ?_⟩
    have := x8c_trψ (fun _ => (0 : Fin 2)) (fun _ => 1) (fun _ => (0 : Fin 2)) (fun _ => 1)
      (1 : Op (Side (fun _ : Fin n => 2) S × Side (fun _ : Fin n => 2) Sᶜ))
    rw [Matrix.one_mul] at this
    rw [this]
    have hp : ((fun _ => (0 : Fin 2)), (fun _ => (0 : Fin 2))) ≠
        (((fun _ => 1) : Side (fun _ : Fin n => 2) S), ((fun _ => 1) : Side (fun _ : Fin n => 2) Sᶜ)) :=
      fun h => ha (congrArg Prod.fst h)
    simp [Matrix.one_apply, hp, Ne.symm hp]; norm_num
  refine ⟨hdens, ?_, hrs, hrg, ?_⟩
  · intro hsep
    have : rg (cutGHZ n S) ≤ 0 := by
      unfold rg robust
      refine csInf_le ⟨0, fun s hs => hs.1⟩ ⟨le_rfl, cutGHZ n S, hdens, fun h => absurd h (by simp), ?_⟩
      unfold mix; simpa using hsep
    linarith
  · intro d hd2 V hV psi C
    obtain ⟨h1, h2, h3⟩ := x8g_emb n hn d hd2 V hV
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · have hr0 : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
        have : (Real.sqrt 2) ≠ 0 := by positivity
        exact inv_ne_zero (by exact_mod_cast this)
      refine @x8c_rank2 (Side d S) (Side d Sᶜ) inferInstance _ (fun k x => ∏ j : {j // j ∈ S}, V j (x j) k)
        (fun k y => ∏ j : {j // j ∈ Sᶜ}, V j (y j) k) ?_ ?_ _ hr0 C ?_
      · intro k l
        exact (x8sum_inst _ _ _).trans (x8c_orth S ⟨j0, hj0⟩ V hV k l)
      · intro k l
        exact (x8sum_inst _ _ _).trans (x8c_orth Sᶜ ⟨j1, by simp [hj1]⟩ V hV k l)
      · intro x y
        exact x8c_Cform S V x y
    · intro h3n
      rw [h2, h3]
      calc (1:ℝ) < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := pow_le_pow_right₀ (by norm_num) (by omega)



end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (n : ℕ) (hn : 2≤n) (S : Finset (Fin n))
  (hne : S.Nonempty) (hproper : S≠Finset.univ) :
  QAlgorithms.IsDensityMatrix (cutGHZ n S) ∧ ¬sep (cutGHZ n S) ∧
  rs (cutGHZ n S)=1 ∧ rg (cutGHZ n S)=1 ∧
  (∀ (d : Fin n → ℕ), (∀ j, 2 ≤ d j) →
    ∀ V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ,
    (∀ j, (V j)ᴴ * V j = 1) →
    let psi : Vec (Config d) := WithLp.toLp 2
      ((localTensor V).mulVec (fun x => ghzKet n true x))
    let C : Matrix (Side d S) (Side d Sᶜ) ℂ := fun x y =>
      psi (fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, by simp [hj]⟩)
    QAlgorithms.IsDensityMatrix (proj psi) ∧
    fsR d false (proj psi) = 1 ∧ fsR d true (proj psi) = (2 : ℝ)^(n-2) ∧
    Matrix.rank C = 2 ∧
    (3 ≤ n → fsR d false (proj psi) < fsR d true (proj psi))) :=
  x8_main n hn S hne hproper
