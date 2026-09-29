-- Prove2me | solution 1 for RobustLS.Structured.worst_case_residual_sdp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:16:55.316363+00:00
-- url     : https://prove2.me/submissions/22d60a76-c43e-4a01-9a00-3ac1d4b1d2e0

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

lemma aux_wcs_dd_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma aux_wcs_add_dd {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (a + b) ⬝ᵥ (a + b) = a ⬝ᵥ a + 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm b a]; ring

lemma aux_wcs_eucNorm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) : eucNorm v ^ 2 = v ⬝ᵥ v := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

lemma aux_wcs_eucNorm_eq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v = Real.sqrt (v ⬝ᵥ v) := by
  unfold eucNorm
  congr 1
  simp [dotProduct, sq]

lemma aux_wcs_resid_vec {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) :
    structMatrix A0 A δ *ᵥ x - structVector b0 b δ = (A0 *ᵥ x - b0) + Mx A b x *ᵥ δ := by
  ext k
  simp only [structMatrix, structVector, Mx, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => δ b * A b k a * x a)]
  have : ∀ i, ∑ j, δ i * A i k j * x j = ∑ j, A i k j * x j * δ i := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  simp only [this, mul_comm (b _ k) (δ _)]
  ring


lemma aux_wcs_gvec_dot {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (d : Fin p → ℝ) :
    gvec A0 A b0 b x ⬝ᵥ d = (A0 *ᵥ x - b0) ⬝ᵥ (Mx A b x *ᵥ d) := by
  rw [gvec, mulVec_transpose, dotProduct_mulVec]

lemma aux_wcs_Fmat_dot {n m p : ℕ}
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (d : Fin p → ℝ) :
    d ⬝ᵥ (Fmat A b x *ᵥ d) = (Mx A b x *ᵥ d) ⬝ᵥ (Mx A b x *ᵥ d) := by
  rw [Fmat, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

lemma aux_wcs_quad {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ t : ℝ) (d : Fin p → ℝ) :
    star (Sum.elim (fun _ : Unit => t) d) ⬝ᵥ
        (calF A0 A b0 b x lam τ *ᵥ Sum.elim (fun _ : Unit => t) d) =
      t ^ 2 * (lam - τ) + τ * (d ⬝ᵥ d) -
      (t • (A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ⬝ᵥ (t • (A0 *ᵥ x - b0) + Mx A b x *ᵥ d) := by
  have h1 : star (Sum.elim (fun _ : Unit => t) d) ⬝ᵥ
        (calF A0 A b0 b x lam τ *ᵥ Sum.elim (fun _ : Unit => t) d) =
      t * t * (lam - τ - hval A0 b0 x) - 2 * t * (gvec A0 A b0 b x ⬝ᵥ d) + τ * (d ⬝ᵥ d)
        - d ⬝ᵥ (Fmat A b x *ᵥ d) := by
    rw [calF, fromBlocks_mulVec, star_trivial, dotProduct, Fintype.sum_sum_type]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      sub_mulVec, smul_mulVec, one_mulVec]
    simp [mulVec, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_sub, mul_add]
    have e1 : ∀ i, d i * (gvec A0 A b0 b x i * t) = t * (gvec A0 A b0 b x i * d i) :=
      fun i => by ring
    have e2 : ∀ i, d i * (τ * d i) = τ * (d i * d i) := fun i => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring
  rw [h1, aux_wcs_Fmat_dot, aux_wcs_gvec_dot, hval, aux_wcs_eucNorm_sq, aux_wcs_add_dd,
    smul_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring


lemma aux_wcs_herm {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ : ℝ) : (calF A0 A b0 b x lam τ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [calF]
  · simp [calF]
  · simp [calF]
  · simp [calF, Fmat, Matrix.mul_apply, Matrix.one_apply, eq_comm, mul_comm]

lemma aux_wcs_sub_dd {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (a - b) ⬝ᵥ (a - b) = a ⬝ᵥ a - 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm b a]; ring

lemma aux_wcs_lower {n p : ℕ} (hp : 1 ≤ p) (w : Fin n → ℝ) (M : Matrix (Fin n) (Fin p) ℝ)
    (lam τ : ℝ)
    (hQ : ∀ (t : ℝ) (d : Fin p → ℝ), 0 ≤ t ^ 2 * (lam - τ) + τ * (d ⬝ᵥ d) -
      (t • w + M *ᵥ d) ⬝ᵥ (t • w + M *ᵥ d)) :
    ∀ δ : Fin p → ℝ, δ ⬝ᵥ δ ≤ 1 → (w + M *ᵥ δ) ⬝ᵥ (w + M *ᵥ δ) ≤ lam := by
  intro δ hδ
  have hτ : 0 ≤ τ := by
    have h := hQ 0 (Pi.single ⟨0, hp⟩ 1)
    simp only [zero_smul, zero_add, single_dotProduct, Pi.single_eq_same] at h
    nlinarith [aux_wcs_dd_nonneg (M *ᵥ Pi.single (⟨0, hp⟩ : Fin p) (1:ℝ))]
  have h := hQ 1 δ
  simp only [one_smul, one_pow, one_mul] at h
  nlinarith [mul_nonneg hτ (sub_nonneg.mpr hδ)]

lemma aux_wcs_small {a C : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ ε ^ 2 * C) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  rcases le_or_gt C 0 with hC | hC
  · have := h 1 one_pos; nlinarith
  · have h1 := h (Real.sqrt (a / (2 * C))) (Real.sqrt_pos.mpr (by positivity))
    rw [Real.sq_sqrt (by positivity)] at h1
    have : a / (2 * C) * C = a / 2 := by field_simp
    linarith


lemma aux_wcs_exists {n p : ℕ} (hp : 1 ≤ p) (w : Fin n → ℝ) (M : Matrix (Fin n) (Fin p) ℝ) :
    ∃ δs : Fin p → ℝ, δs ⬝ᵥ δs = 1 ∧ ∃ τ : ℝ, ∀ (t : ℝ) (d : Fin p → ℝ),
      0 ≤ t ^ 2 * ((w + M *ᵥ δs) ⬝ᵥ (w + M *ᵥ δs) - τ) + τ * (d ⬝ᵥ d) -
        (t • w + M *ᵥ d) ⬝ᵥ (t • w + M *ᵥ d) := by
  set S : Set (Fin p → ℝ) := {δ | δ ⬝ᵥ δ = 1} with hS
  have hcont : Continuous fun δ : Fin p → ℝ => δ ⬝ᵥ δ :=
    Continuous.dotProduct continuous_id continuous_id
  have hSc : IsCompact S := by
    have hcl : IsClosed S := isClosed_eq hcont continuous_const
    refine (isCompact_closedBall (0 : Fin p → ℝ) 1).of_isClosed_subset hcl ?_
    intro δ hδ
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    have hδ' : ∑ j, δ j * δ j = 1 := hδ
    have h1 := Finset.single_le_sum (f := fun j => δ j * δ j)
      (fun j _ => mul_self_nonneg (δ j)) (Finset.mem_univ i)
    simp only [hδ'] at h1
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hne : S.Nonempty := ⟨Pi.single ⟨0, hp⟩ 1, by simp [hS]⟩
  have hlin : Continuous fun δ : Fin p → ℝ => w + M *ᵥ δ :=
    continuous_const.add (Continuous.matrix_mulVec continuous_const continuous_id)
  have hφ : Continuous fun δ : Fin p → ℝ => (w + M *ᵥ δ) ⬝ᵥ (w + M *ᵥ δ) :=
    hlin.dotProduct hlin
  obtain ⟨δs, hδsS, hmax⟩ := hSc.exists_isMaxOn hne hφ.continuousOn
  have hδs : δs ⬝ᵥ δs = 1 := hδsS
  refine ⟨δs, hδs, ?_⟩
  set r := w + M *ᵥ δs with hr
  set g := r ᵥ* M with hg
  set τ := g ⬝ᵥ δs with hτ
  have hrM : ∀ e, r ⬝ᵥ (M *ᵥ e) = g ⬝ᵥ e := fun e => dotProduct_mulVec r M e
  have KL : ∀ e : Fin p → ℝ, 2 * (δs ⬝ᵥ e) + e ⬝ᵥ e = 0 →
      2 * (g ⬝ᵥ e) + (M *ᵥ e) ⬝ᵥ (M *ᵥ e) ≤ 0 := by
    intro e he
    have hmem : δs + e ∈ S := by
      show (δs + e) ⬝ᵥ (δs + e) = 1
      rw [aux_wcs_add_dd]; linarith
    have h := isMaxOn_iff.mp hmax _ hmem
    have hv : w + M *ᵥ (δs + e) = r + M *ᵥ e := by rw [mulVec_add, hr, add_assoc]
    rw [hv, ← hr, aux_wcs_add_dd r (M *ᵥ e), hrM] at h
    linarith
  -- first-order condition
  have hgi : g = τ • δs := by
    set u := g - τ • δs with hu
    have hu0 : δs ⬝ᵥ u = 0 := by
      rw [hu, dotProduct_sub, dotProduct_smul, hδs, dotProduct_comm, ← hτ]; simp
    have hu0' : u ⬝ᵥ δs = 0 := by rw [dotProduct_comm]; exact hu0
    have hgu : g ⬝ᵥ u = u ⬝ᵥ u := by
      have : g = u + τ • δs := by rw [hu]; abel
      rw [this, add_dotProduct, smul_dotProduct, hu0]; simp
    have hbound : ∀ c : ℝ, 0 < c → u ⬝ᵥ u ≤ c * τ := by
      intro c hc
      have hU := aux_wcs_dd_nonneg u
      have hpos : 0 < u ⬝ᵥ u + c ^ 2 := by positivity
      set s := 2 * c / (u ⬝ᵥ u + c ^ 2) with hs
      have hs0 : 0 < s := by positivity
      have hsU : s * (u ⬝ᵥ u + c ^ 2) = 2 * c := by rw [hs]; field_simp
      have h := KL (s • (u - c • δs)) (by
        rw [dotProduct_smul, dotProduct_sub, dotProduct_smul, hu0, hδs, smul_dotProduct,
          dotProduct_smul, aux_wcs_sub_dd, dotProduct_smul, smul_dotProduct, dotProduct_smul,
          hu0', hδs]
        simp only [smul_eq_mul]
        linear_combination s * hsU)
      rw [dotProduct_smul, dotProduct_sub, dotProduct_smul, hgu, ← hτ, mulVec_smul,
        smul_dotProduct, dotProduct_smul] at h
      have hK := aux_wcs_dd_nonneg (M *ᵥ (u - c • δs))
      simp only [smul_eq_mul] at h
      have h2 : 0 ≤ s * (s * (M *ᵥ (u - c • δs)) ⬝ᵥ (M *ᵥ (u - c • δs))) := by positivity
      have h3 : s * (u ⬝ᵥ u - c * τ) ≤ 0 := by nlinarith
      by_contra hcon
      push Not at hcon
      have := mul_pos hs0 (sub_pos.mpr hcon)
      linarith
    have hU0 : u ⬝ᵥ u = 0 := by
      have hU := aux_wcs_dd_nonneg u
      by_contra hne
      have hUpos : 0 < u ⬝ᵥ u := lt_of_le_of_ne hU (Ne.symm hne)
      have h := hbound (u ⬝ᵥ u / (2 * (|τ| + 1))) (by positivity)
      have : u ⬝ᵥ u / (2 * (|τ| + 1)) * τ ≤ u ⬝ᵥ u / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [le_abs_self τ, abs_nonneg τ]
      linarith
    have : g - τ • δs = 0 := dotProduct_self_eq_zero.mp hU0
    exact sub_eq_zero.mp this
  have hL : ∀ v, g ⬝ᵥ v = τ * (δs ⬝ᵥ v) := fun v => by rw [hgi, smul_dotProduct, smul_eq_mul]
  -- second-order condition
  have hc1 : ∀ v : Fin p → ℝ, δs ⬝ᵥ v ≠ 0 → (M *ᵥ v) ⬝ᵥ (M *ᵥ v) ≤ τ * (v ⬝ᵥ v) := by
    intro v hσ
    have hE : 0 < v ⬝ᵥ v := by
      rcases (aux_wcs_dd_nonneg v).lt_or_eq with h | h
      · exact h
      · exfalso
        have := dotProduct_self_eq_zero.mp h.symm
        rw [this, dotProduct_zero] at hσ
        exact hσ rfl
    set s := -2 * (δs ⬝ᵥ v) / (v ⬝ᵥ v) with hs
    have hsE : s * (v ⬝ᵥ v) = -2 * (δs ⬝ᵥ v) := by rw [hs]; field_simp
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact div_ne_zero (mul_ne_zero (by norm_num) hσ) hE.ne'
    have h := KL (s • v) (by
      rw [dotProduct_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      linear_combination s * hsE)
    rw [dotProduct_smul, hL, mulVec_smul, smul_dotProduct, dotProduct_smul] at h
    simp only [smul_eq_mul] at h
    have hs2 : 0 < s ^ 2 := by positivity
    have hX : s ^ 2 * ((M *ᵥ v) ⬝ᵥ (M *ᵥ v) - τ * (v ⬝ᵥ v)) =
        2 * (s * (τ * (δs ⬝ᵥ v))) + s * (s * (M *ᵥ v) ⬝ᵥ (M *ᵥ v)) := by
      linear_combination (-s * τ) * hsE
    by_contra hcon
    push Not at hcon
    have := mul_pos hs2 (sub_pos.mpr hcon)
    linarith
  have hc : ∀ v : Fin p → ℝ, (M *ᵥ v) ⬝ᵥ (M *ᵥ v) ≤ τ * (v ⬝ᵥ v) := by
    intro v
    by_cases hσ : δs ⬝ᵥ v = 0
    · have key : ∀ ε : ℝ, 0 < ε → (M *ᵥ v) ⬝ᵥ (M *ᵥ v) - τ * (v ⬝ᵥ v) ≤ ε ^ 2 * τ := by
        intro ε hε
        have h1 := hc1 (v + ε • δs) (by
          rw [dotProduct_add, dotProduct_smul, hσ, hδs]; simp; exact hε.ne')
        have h2 := hc1 (v - ε • δs) (by
          rw [dotProduct_sub, dotProduct_smul, hσ, hδs]; simp; exact hε.ne')
        rw [mulVec_add, mulVec_smul, aux_wcs_add_dd, aux_wcs_add_dd] at h1
        rw [mulVec_sub, mulVec_smul, aux_wcs_sub_dd, aux_wcs_sub_dd] at h2
        simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2
        rw [dotProduct_comm v δs, hσ, hδs] at h1 h2
        have hKd := mul_nonneg (sq_nonneg ε) (aux_wcs_dd_nonneg (M *ᵥ δs))
        nlinarith
      exact sub_nonpos.mp (aux_wcs_small key)
    · exact hc1 v hσ
  refine ⟨τ, fun t d => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + t • δs := ⟨d - t • δs, by abel⟩
  have hvec : t • w + M *ᵥ (e + t • δs) = t • r + M *ᵥ e := by
    rw [mulVec_add, mulVec_smul, hr, smul_add]; abel
  rw [hvec, aux_wcs_add_dd (t • r) (M *ᵥ e), aux_wcs_add_dd e (t • δs)]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hrM, hL, dotProduct_comm e δs, hδs]
  have := hc e
  nlinarith

end RobustLS.Structured

open RobustLS.Structured
open Matrix

theorem solution {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) :
    (∀ lam τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef → rS A0 A b0 b 1 x ^ 2 ≤ lam) ∧
      ∃ τ : ℝ, (calF A0 A b0 b x (rS A0 A b0 b 1 x ^ 2) τ).PosSemidef := by
  have hpsd : ∀ lam τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef ↔
      ∀ (t : ℝ) (d : Fin p → ℝ), 0 ≤ t ^ 2 * (lam - τ) + τ * (d ⬝ᵥ d) -
        (t • (A0 *ᵥ x - b0) + Mx A b x *ᵥ d) ⬝ᵥ (t • (A0 *ᵥ x - b0) + Mx A b x *ᵥ d) := by
    intro lam τ
    rw [posSemidef_iff_dotProduct_mulVec]
    constructor
    · rintro ⟨-, h⟩ t d
      rw [← aux_wcs_quad]
      exact h _
    · intro h
      refine ⟨aux_wcs_herm A0 A b0 b x lam τ, fun z => ?_⟩
      have hz : z = Sum.elim (fun _ : Unit => z (Sum.inl ())) (z ∘ Sum.inr) := by
        ext i
        rcases i with ⟨⟩ | i <;> rfl
      rw [hz, aux_wcs_quad]
      exact h _ _
  have hres : ∀ δ, structuredResidual A0 A b0 b x δ =
      Real.sqrt ((A0 *ᵥ x - b0 + Mx A b x *ᵥ δ) ⬝ᵥ (A0 *ᵥ x - b0 + Mx A b x *ᵥ δ)) := by
    intro δ
    rw [structuredResidual, aux_wcs_resid_vec, aux_wcs_eucNorm_eq]
  have hball : ∀ δ : Fin p → ℝ, eucNorm δ ≤ 1 → δ ⬝ᵥ δ ≤ 1 := by
    intro δ h
    rw [← aux_wcs_eucNorm_sq]
    have h0 : 0 ≤ eucNorm δ := Real.sqrt_nonneg _
    nlinarith
  have hup : ∀ lam τ : ℝ, (calF A0 A b0 b x lam τ).PosSemidef →
      BddAbove {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧ r = structuredResidual A0 A b0 b x δ} ∧
        rS A0 A b0 b 1 x ^ 2 ≤ lam := by
    intro lam τ h
    have hl := aux_wcs_lower hp _ _ lam τ ((hpsd lam τ).mp h)
    have hbd : ∀ r ∈ {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧
        r = structuredResidual A0 A b0 b x δ}, r ≤ Real.sqrt lam := by
      rintro r ⟨δ, hδ, rfl⟩
      rw [hres]
      exact Real.sqrt_le_sqrt (hl δ (hball δ hδ))
    have hmem0 : structuredResidual A0 A b0 b x 0 ∈ {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧
        r = structuredResidual A0 A b0 b x δ} := ⟨0, by simp [eucNorm], rfl⟩
    have hBdd : BddAbove {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧
        r = structuredResidual A0 A b0 b x δ} := ⟨_, hbd⟩
    refine ⟨hBdd, ?_⟩
    have h1 : rS A0 A b0 b 1 x ≤ Real.sqrt lam := csSup_le ⟨_, hmem0⟩ hbd
    have h0 : 0 ≤ rS A0 A b0 b 1 x :=
      le_trans (by rw [hres]; exact Real.sqrt_nonneg _) (le_csSup hBdd hmem0)
    have hlam : 0 ≤ lam := le_trans (aux_wcs_dd_nonneg _) (hl 0 (by simp))
    calc rS A0 A b0 b 1 x ^ 2 ≤ Real.sqrt lam ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = lam := Real.sq_sqrt hlam
  obtain ⟨δs, hδs, τ, hQ⟩ := aux_wcs_exists hp (A0 *ᵥ x - b0) (Mx A b x)
  have hPS := (hpsd _ τ).mpr hQ
  obtain ⟨hBdd, hle⟩ := hup _ τ hPS
  have hge : (A0 *ᵥ x - b0 + Mx A b x *ᵥ δs) ⬝ᵥ (A0 *ᵥ x - b0 + Mx A b x *ᵥ δs) ≤
      rS A0 A b0 b 1 x ^ 2 := by
    have hmem : structuredResidual A0 A b0 b x δs ∈ {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧
        r = structuredResidual A0 A b0 b x δ} :=
      ⟨δs, by rw [aux_wcs_eucNorm_eq, hδs, Real.sqrt_one], rfl⟩
    have h1 := le_csSup hBdd hmem
    rw [hres] at h1
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (aux_wcs_dd_nonneg _)] at this
  have heq := le_antisymm hle hge
  refine ⟨fun lam τ' h => (hup lam τ' h).2, τ, ?_⟩
  rw [heq]
  exact hPS
