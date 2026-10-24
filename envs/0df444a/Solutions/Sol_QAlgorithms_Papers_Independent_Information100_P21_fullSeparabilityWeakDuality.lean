-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.fullSeparabilityWeakDuality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:01:43.357126+00:00
-- url     : https://prove2.me/submissions/b7c69e86-4902-47dc-b64c-5c4c8d6ae69d

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

theorem x8_main {P : Type*} [Fintype P] (d : P → ℕ) (hd : ∀ j,0<d j)
  (rho Z : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) (hZ : Z.IsHermitian) :
  ((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re ∧ (Z*sigma).trace.re≤1) →
    -(Z*rho).trace.re≤fsR d true rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → tau∈fs d → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) ∧
  (((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re) ∧ (1-Z).PosSemidef) →
    -(Z*rho).trace.re≤fsR d false rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → QAlgorithms.IsDensityMatrix tau → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) := by
  obtain ⟨s0, hs0, ω0, hω0, hω0F, hmix0⟩ := x8f_feas hd hr
  constructor
  · intro hW
    have hdual : ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → tau∈fs d → sigma∈fs d →
        rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t := by
      intro t τ σ ht hτ hσ heq
      have e := x8f_eq rho τ σ Z t heq
      have h1 := (hW τ hτ).2
      have h2 := (hW σ hσ).1
      nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_nonneg (by linarith : (0:ℝ) ≤ 1 + t) h2]
    refine ⟨?_, hdual⟩
    unfold fsR robust
    refine le_csInf ⟨s0, hs0, ω0, hω0, fun _ => hω0F, hmix0⟩ ?_
    rintro s ⟨hs, ω, hω, hωF, hmix⟩
    exact hdual s ω _ hs (hωF rfl) hmix (x8f_mix rho ω hs)
  · rintro ⟨hW, h1Z⟩
    have hdual : ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → QAlgorithms.IsDensityMatrix tau →
        sigma∈fs d → rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t := by
      intro t τ σ ht hτ hσ heq
      have e := x8f_eq rho τ σ Z t heq
      have h1 : (Z * τ).trace.re ≤ 1 := by
        have := x8f_tr_psd h1Z hτ.1
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hτ.2] at this
        simp at this; linarith
      have h2 := hW σ hσ
      nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_nonneg (by linarith : (0:ℝ) ≤ 1 + t) h2]
    refine ⟨?_, hdual⟩
    unfold fsR robust
    refine le_csInf ⟨s0, hs0, ω0, hω0, fun h => absurd h (by simp), hmix0⟩ ?_
    rintro s ⟨hs, ω, hω, _, hmix⟩
    exact hdual s ω _ hs hω hmix (x8f_mix rho ω hs)

end

end QAlgorithms.Papers.Independent.Information100.P21

section
attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {P : Type*} [Fintype P] (d : P → ℕ) (hd : ∀ j,0<d j)
  (rho Z : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) (hZ : Z.IsHermitian) :
  ((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re ∧ (Z*sigma).trace.re≤1) →
    -(Z*rho).trace.re≤fsR d true rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → tau∈fs d → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) ∧
  (((∀ sigma : Op (Config d), sigma∈fs d → 0≤(Z*sigma).trace.re) ∧ (1-Z).PosSemidef) →
    -(Z*rho).trace.re≤fsR d false rho ∧
    ∀ (t : ℝ) (tau sigma : Op (Config d)), 0≤t → QAlgorithms.IsDensityMatrix tau → sigma∈fs d →
      rho+(t:ℂ) • tau=(1+t:ℂ) • sigma → -(Z*rho).trace.re≤t) :=
  x8_main d hd rho Z hr hZ

end
