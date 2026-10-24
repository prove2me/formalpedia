-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.freeMapsSpectatorsEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T13:05:34.086997+00:00
-- url     : https://prove2.me/submissions/bc38a17e-a38e-455b-a49c-43674722adaf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

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

theorem x8_main {Q : Type*} [Fintype Q]
  (d : P → ℕ) (e : Q → ℕ) (hd : ∀ j,0<d j) (he : ∀ j,0<e j)
  (Phi : QAlgorithms.Superop (Config d) (Config e)) (hc : QAlgorithms.IsChannel Phi)
  (hf : ∀ sigma, sigma∈fs d → Phi sigma∈fs e)
  (rho : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) :
  (∀ standard : Bool, fsR e standard (Phi rho)≤fsR d standard rho) ∧
  ((∃ Psi : QAlgorithms.Superop (Config e) (Config d), QAlgorithms.IsChannel Psi ∧
      (∀ sigma, sigma∈fs e → Psi sigma∈fs d) ∧ (∀ X, Psi (Phi X)=X)) →
    ∀ standard : Bool, fsR e standard (Phi rho)=fsR d standard rho) ∧
  (∀ eta : Op (Config e), eta∈fs e → ∀ standard : Bool,
    fsR (Sum.elim d e) standard (spectator rho eta)=fsR d standard rho) ∧
  (∀ (f : P → ℕ) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ),
    (∀ j,0<f j) → (∀ j,(V j)ᴴ*V j=1) → ∀ standard : Bool,
    fsR f standard (localTensor V*rho*(localTensor V)ᴴ)=fsR d standard rho) := by
  have h1 := (x8m_chan hd Phi hc hf rho hr).2
  refine ⟨h1, ?_, ?_, ?_⟩
  · rintro ⟨Psi, hPsi, hPsif, hinv⟩ std
    have hdens := (x8m_chan hd Phi hc hf rho hr).1
    have := (x8m_chan he Psi hPsi hPsif (Phi rho) hdens).2 std
    rw [hinv] at this
    exact le_antisymm (h1 std) this
  · intro η hη std
    have hηd := x8m_fs_dens hη
    have hdS : ∀ j, 0 < Sum.elim d e j := fun j => by cases j with
      | inl a => exact hd a
      | inr b => exact he b
    apply le_antisymm
    · obtain ⟨s, hs, ω, hω, hωF, hm⟩ := x8f_feas hd hr
      have := x8m_mono (FA := fs d) (FB := fs (Sum.elim d e)) std (x8T1 η)
        (fun X hX => by show QAlgorithms.IsDensityMatrix (spectator X η); exact x8s_dens hX hηd) (fun X hX => x8s_fs hX hη)
        ⟨s, hs, ω, hω, fun _ => hωF, hm⟩
      rw [x8T1_apply] at this
      unfold fsR
      exact (x8rob_inst _ _ _ _ _).trans_le this
    · have hsd : QAlgorithms.IsDensityMatrix (spectator rho η) := x8s_dens hr hηd
      obtain ⟨s, hs, ω, hω, hωF, hm⟩ := x8f_feas (P := P ⊕ Q) (d := Sum.elim d e) hdS
        (x8dens_inst _ _ _ hsd)
      have := x8m_mono (FA := fs (Sum.elim d e)) (FB := fs d) std (x8K (x8B (d := d) (e := e)))
        (fun Y hY => x8T2_dens Y hY)
        (fun Y hY => x8T2_fs hY) ⟨s, hs, ω, x8dens_inst _ _ _ hω, fun _ => hωF, hm⟩
      rw [x8T2_spec rho hηd.2] at this
      unfold fsR
      exact this.trans_eq (x8rob_inst _ _ _ _ _)
  · intro f V hf0 hV std
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

end

end QAlgorithms.Papers.Independent.Information100.P21

section
attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {P Q : Type*} [Fintype P] [Fintype Q]
  (d : P → ℕ) (e : Q → ℕ) (hd : ∀ j,0<d j) (he : ∀ j,0<e j)
  (Phi : QAlgorithms.Superop (Config d) (Config e)) (hc : QAlgorithms.IsChannel Phi)
  (hf : ∀ sigma, sigma∈fs d → Phi sigma∈fs e)
  (rho : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) :
  (∀ standard : Bool, fsR e standard (Phi rho)≤fsR d standard rho) ∧
  ((∃ Psi : QAlgorithms.Superop (Config e) (Config d), QAlgorithms.IsChannel Psi ∧
      (∀ sigma, sigma∈fs e → Psi sigma∈fs d) ∧ (∀ X, Psi (Phi X)=X)) →
    ∀ standard : Bool, fsR e standard (Phi rho)=fsR d standard rho) ∧
  (∀ eta : Op (Config e), eta∈fs e → ∀ standard : Bool,
    fsR (Sum.elim d e) standard (spectator rho eta)=fsR d standard rho) ∧
  (∀ (f : P → ℕ) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ),
    (∀ j,0<f j) → (∀ j,(V j)ᴴ*V j=1) → ∀ standard : Bool,
    fsR f standard (localTensor V*rho*(localTensor V)ᴴ)=fsR d standard rho) :=
  x8_main d e hd he Phi hc hf rho hr

end
