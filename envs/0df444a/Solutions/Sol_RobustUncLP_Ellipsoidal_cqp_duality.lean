-- Prove2me | solution 1 for RobustUncLP.Ellipsoidal.cqp_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:19:10.82562+00:00
-- url     : https://prove2.me/submissions/06f68f31-5c96-483b-8657-3695f1097f46

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_CQP



namespace RobustUncLP.Ellipsoidal

open Matrix CQPData

section Aux

lemma en_nonneg {M : ℕ} (v : Fin M → ℝ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma en_sq {M : ℕ} (v : Fin M → ℝ) : euclidNorm v ^ 2 = ∑ j, v j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma en_smul {M : ℕ} (c : ℝ) (v : Fin M → ℝ) : euclidNorm (c • v) = |c| * euclidNorm v := by
  unfold euclidNorm
  have : ∑ j, (c • v) j ^ 2 = c ^ 2 * ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma en_eq_norm {M : ℕ} (v : Fin M → ℝ) :
    euclidNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin M))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclidNorm
  simp

lemma en_add_le {M : ℕ} (v w : Fin M → ℝ) : euclidNorm (v + w) ≤ euclidNorm v + euclidNorm w := by
  rw [en_eq_norm, en_eq_norm, en_eq_norm]
  exact norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin M)) (WithLp.toLp 2 w)

lemma en_zero {M : ℕ} : euclidNorm (0 : Fin M → ℝ) = 0 := by
  simp [euclidNorm]

lemma en_cs {M : ℕ} (a b : Fin M → ℝ) : |a ⬝ᵥ b| ≤ euclidNorm a * euclidNorm b := by
  unfold euclidNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  apply Real.abs_le_sqrt
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simpa [dotProduct] using this

end Aux

lemma weak_dual {N p k : ℕ} (P : CQPData N p k) (z : Fin N → ℝ) (hz : z ∈ P.primalFeas)
    (w) (hw : w ∈ P.dualFeas) : P.dualObj w ≤ P.primalObj z := by
  obtain ⟨hR, hc⟩ := hz
  obtain ⟨he, hn⟩ := hw
  have h1 : P.e ⬝ᵥ z = P.r ⬝ᵥ w.1 + ∑ ℓ, (w.2.2 ℓ * (P.c ℓ ⬝ᵥ z) + w.2.1 ℓ ⬝ᵥ (P.A ℓ *ᵥ z)) := by
    conv_lhs => rw [← he]
    rw [add_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hR]
    congr 1
    · exact dotProduct_comm _ _
    · rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [add_dotProduct, smul_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      simp [smul_eq_mul]
  have h2 : ∀ ℓ, 0 ≤ w.2.2 ℓ * (P.c ℓ ⬝ᵥ z - P.d ℓ) + w.2.1 ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ) := by
    intro ℓ
    have hy := hc ℓ
    have hm := hn ℓ
    have hcs := en_cs (w.2.1 ℓ) (P.A ℓ *ᵥ z - P.b ℓ)
    have hy0 := en_nonneg (P.A ℓ *ᵥ z - P.b ℓ)
    have hm0 := en_nonneg (w.2.1 ℓ)
    have := neg_abs_le (w.2.1 ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ))
    nlinarith [mul_le_mul_of_nonneg_left hy (hm0.trans hm), mul_le_mul_of_nonneg_right hm hy0]
  have h3 := Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ Finset.univ) => h2 ℓ)
  unfold dualObj primalObj
  rw [h1]
  have : ∑ ℓ, (w.2.2 ℓ * (P.c ℓ ⬝ᵥ z - P.d ℓ) + w.2.1 ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ)) =
      ∑ ℓ, (w.2.2 ℓ * (P.c ℓ ⬝ᵥ z) + w.2.1 ℓ ⬝ᵥ (P.A ℓ *ᵥ z)) -
        ∑ ℓ, (P.d ℓ * w.2.2 ℓ + P.b ℓ ⬝ᵥ w.2.1 ℓ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [dotProduct_sub, dotProduct_comm (P.b ℓ)]
    ring
  linarith

/-- affine function nonneg on affine subspace `Rz = r` => linear part in range of `Rᵀ`. -/
lemma la_range {N p : ℕ} (R : Matrix (Fin p) (Fin N) ℝ) (r : Fin p → ℝ) (z0 : Fin N → ℝ)
    (hz0 : R *ᵥ z0 = r) (a : Fin N → ℝ) (κ : ℝ)
    (h : ∀ z, R *ᵥ z = r → 0 ≤ a ⬝ᵥ z + κ) : ∃ ρ : Fin p → ℝ, a = Rᵀ *ᵥ ρ := by
  have hker : ∀ δ, R *ᵥ δ = 0 → a ⬝ᵥ δ = 0 := by
    intro δ hδ
    by_contra hne
    set s := a ⬝ᵥ z0 + κ with hs
    have hz : R *ᵥ (z0 + (-(s + 1) / (a ⬝ᵥ δ)) • δ) = r := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hδ, hz0]; simp
    have := h _ hz
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have e : -(s + 1) / (a ⬝ᵥ δ) * (a ⬝ᵥ δ) = -(s + 1) := by field_simp
    nlinarith
  let L : Fin p → (Fin N → ℝ) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun z => (R *ᵥ z) i
      map_add' := by intro x y; simp [Matrix.mulVec_add]
      map_smul' := by intro c x; simp [Matrix.mulVec_smul] }
  let K : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => a ⬝ᵥ z
      map_add' := by intro x y; simp [dotProduct_add]
      map_smul' := by intro c x; simp [dotProduct_smul] }
  have hle : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker K := by
    intro δ hδ
    rw [Submodule.mem_iInf] at hδ
    have : R *ᵥ δ = 0 := by
      ext i; exact LinearMap.mem_ker.1 (hδ i)
    exact hker δ this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hle)
  refine ⟨c, ?_⟩
  ext j
  have := congrArg (fun F => F (Pi.single j 1)) hc
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
  simp [K, L, mulVec, dotProduct, Pi.single_apply] at this ⊢
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


/-- the ambient space of the separation argument -/
abbrev Esp {k : ℕ} (q : Fin (k + 1) → ℕ) :=
  ℝ × (Fin (k + 1) → ℝ) × ((ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ)

def GSet {k : ℕ} (q : Fin (k + 1) → ℕ) : Set (Esp q) :=
  {g | g.1 < 0 ∧ ∀ ℓ, euclidNorm (g.2.2 ℓ) < g.2.1 ℓ}

lemma GSet_convex {k : ℕ} (q : Fin (k + 1) → ℕ) : Convex ℝ (GSet q) := by
  rintro g1 ⟨h1s, h1⟩ g2 ⟨h2s, h2⟩ a b ha hb hab
  refine ⟨?_, fun ℓ => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rcases ha.eq_or_lt with h | h
    · subst h
      have : b = 1 := by linarith
      subst this; simpa using h2s
    · nlinarith [mul_pos h (neg_pos.2 h1s), mul_nonneg hb (neg_pos.2 h2s).le]
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have e1 := en_add_le (a • g1.2.2 ℓ) (b • g2.2.2 ℓ)
    rw [en_smul, en_smul, abs_of_nonneg ha, abs_of_nonneg hb] at e1
    have := h1 ℓ
    have := h2 ℓ
    rcases ha.eq_or_lt with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      simp only [zero_smul, zero_add, one_smul, zero_mul] at e1 ⊢
      linarith
    · nlinarith [mul_pos h (sub_pos.2 (h1 ℓ)), mul_nonneg hb (sub_pos.2 (h2 ℓ)).le]

lemma GSet_isOpen {k : ℕ} (q : Fin (k + 1) → ℕ) : IsOpen (GSet q) := by
  have h1 : IsOpen {g : Esp q | g.1 < 0} := isOpen_lt continuous_fst continuous_const
  have h2 : ∀ ℓ, IsOpen {g : Esp q | euclidNorm (g.2.2 ℓ) < g.2.1 ℓ} := by
    intro ℓ
    refine isOpen_lt ?_ ?_
    · unfold euclidNorm
      fun_prop
    · fun_prop
  have : GSet q = {g : Esp q | g.1 < 0} ∩ ⋂ ℓ, {g : Esp q | euclidNorm (g.2.2 ℓ) < g.2.1 ℓ} := by
    ext g; simp [GSet]
  rw [this]
  exact h1.inter (isOpen_iInter_of_finite h2)

def PhiMap {N p k : ℕ} (P : CQPData N p k) (v : ℝ) (z : Fin N → ℝ) : Esp P.q :=
  (P.primalObj z - v, fun ℓ => P.c ℓ ⬝ᵥ z - P.d ℓ, fun ℓ => P.A ℓ *ᵥ z - P.b ℓ)

lemma T_convex {N p k : ℕ} (P : CQPData N p k) (v : ℝ) :
    Convex ℝ (PhiMap P v '' {z | P.R *ᵥ z = P.r}) := by
  rintro _ ⟨z1, h1, rfl⟩ _ ⟨z2, h2, rfl⟩ a b ha hb hab
  refine ⟨a • z1 + b • z2, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, ← add_smul, hab,
      one_smul]
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [PhiMap, primalObj, dotProduct_add, dotProduct_smul, smul_eq_mul, Prod.fst_add,
        Prod.smul_fst]
      linear_combination (-(P.φ - v)) * hab
    · funext ℓ
      simp only [PhiMap, dotProduct_add, dotProduct_smul, smul_eq_mul, Prod.snd_add,
        Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply]
      linear_combination (P.d ℓ) * hab
    · funext ℓ
      ext j
      simp only [PhiMap, Matrix.mulVec_add, Matrix.mulVec_smul, Prod.snd_add,
        Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      linear_combination (P.b ℓ j) * hab

lemma lim_pos (c u : ℝ) (h : ∀ ε > 0, ε * c < u) : 0 ≤ u := by
  by_contra hu
  replace hu := not_le.1 hu
  have hc : 0 < 2 * (|c| + 1) := by positivity
  have := h (-u / (2 * (|c| + 1))) (by apply div_pos <;> linarith)
  have e : -u / (2 * (|c| + 1)) * c ≥ -(-u / (2 * (|c| + 1)) * |c|) := by
    nlinarith [neg_abs_le c, div_pos (neg_pos.2 hu) hc]
  have e2 : -u / (2 * (|c| + 1)) * (|c| + 1) = -u / 2 := by field_simp
  have e3 : 0 < -u / (2 * (|c| + 1)) := div_pos (neg_pos.2 hu) hc
  nlinarith

lemma lim_zero (x c : ℝ) (h : ∀ ε > 0, x ≤ ε * c) : x ≤ 0 := by
  by_contra hx
  replace hx := not_le.1 hx
  have hc : 0 < 2 * (|c| + 1) := by positivity
  have := h (x / (2 * (|c| + 1))) (by positivity)
  have e : x / (2 * (|c| + 1)) * c ≤ x / (2 * (|c| + 1)) * |c| :=
    mul_le_mul_of_nonneg_left (le_abs_self c) (by positivity)
  have e2 : x / (2 * (|c| + 1)) * (|c| + 1) = x / 2 := by field_simp
  have e3 : 0 < x / (2 * (|c| + 1)) := by positivity
  nlinarith


lemma lin_dot {n : ℕ} (g : (Fin n → ℝ) →ₗ[ℝ] ℝ) : ∃ c : Fin n → ℝ, ∀ y, g y = c ⬝ᵥ y := by
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), fun y => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ g y]
  simp [dotProduct, mul_comm]

lemma lin_dep {k : ℕ} (q : Fin (k + 1) → ℕ)
    (g : ((ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ) →ₗ[ℝ] ℝ) :
    ∃ μ : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ, ∀ y, g y = ∑ ℓ, μ ℓ ⬝ᵥ y ℓ := by
  have h : ∀ ℓ, ∃ c : Fin (q ℓ) → ℝ, ∀ y, g (Pi.single ℓ y) = c ⬝ᵥ y := fun ℓ =>
    lin_dot (g.comp (LinearMap.single ℝ (fun ℓ => Fin (q ℓ) → ℝ) ℓ))
  choose μ hμ using h
  refine ⟨μ, fun y => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun ℓ _ => hμ ℓ (y ℓ)

lemma expand {k : ℕ} (q : Fin (k + 1) → ℕ) (f : Esp q →ₗ[ℝ] ℝ) :
    ∃ (α : ℝ) (ν : Fin (k + 1) → ℝ) (μ : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ),
      ∀ s t y, f (s, t, y) = α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ := by
  obtain ⟨ν, hν⟩ := lin_dot (f.comp ((LinearMap.inr ℝ ℝ _).comp (LinearMap.inl ℝ _ _)))
  obtain ⟨μ, hμ⟩ := lin_dep q (f.comp ((LinearMap.inr ℝ ℝ _).comp (LinearMap.inr ℝ _ _)))
  refine ⟨f (1, 0, 0), ν, μ, fun s t y => ?_⟩
  have e : ((s, t, y) : Esp q) = s • ((1, 0, 0) : Esp q) + (0, t, 0) + (0, 0, y) := by
    ext <;> simp
  rw [e, map_add, map_add, map_smul]
  have h1 := hν t
  have h2 := hμ y
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.inl_apply] at h1 h2
  rw [h1, h2]
  simp [dotProduct, smul_eq_mul, mul_comm]

/-- consequences of the separation, in terms of the coefficients -/
lemma sep_consequences {k : ℕ} (q : Fin (k + 1) → ℕ) (α : ℝ) (ν : Fin (k + 1) → ℝ)
    (μ : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ) (u : ℝ)
    (hG : ∀ (s : ℝ) (t : Fin (k + 1) → ℝ) (y : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ),
      s < 0 → (∀ ℓ, euclidNorm (y ℓ) < t ℓ) →
        α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ < u) :
    0 ≤ u ∧ 0 ≤ α ∧ ∀ ℓ, euclidNorm (μ ℓ) ≤ -ν ℓ := by
  -- cone property
  have ha : ∀ (s : ℝ) (t : Fin (k + 1) → ℝ) (y : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ),
      s < 0 → (∀ ℓ, euclidNorm (y ℓ) < t ℓ) →
        α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ ≤ 0 := by
    intro s t y hs hy
    by_contra hpos
    replace hpos := not_le.1 hpos
    set F := α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ with hF
    have lam : 0 < (|u| + 1) / F := by positivity
    have := hG (((|u| + 1) / F) * s) (((|u| + 1) / F) • t) (((|u| + 1) / F) • y)
      (mul_neg_of_pos_of_neg lam hs) (fun ℓ => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [en_smul, abs_of_pos lam]
        exact mul_lt_mul_of_pos_left (hy ℓ) lam)
    have e1 : ∑ ℓ, ν ℓ * ((((|u| + 1) / F) • t) ℓ) = ((|u| + 1) / F) * ∑ ℓ, ν ℓ * t ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    have e2 : ∑ ℓ, μ ℓ ⬝ᵥ ((((|u| + 1) / F) • y) ℓ)
        = ((|u| + 1) / F) * ∑ ℓ, μ ℓ ⬝ᵥ y ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [Pi.smul_apply, dotProduct_smul, smul_eq_mul]
    have e : α * (((|u| + 1) / F) * s) + ∑ ℓ, ν ℓ * ((((|u| + 1) / F) • t) ℓ)
        + ∑ ℓ, μ ℓ ⬝ᵥ ((((|u| + 1) / F) • y) ℓ) = ((|u| + 1) / F) * F := by
      rw [e1, e2, hF]; ring
    rw [e, div_mul_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self u]
  -- u ≥ 0
  have hu : 0 ≤ u := by
    refine lim_pos (-α + ∑ ℓ, ν ℓ) u fun ε hε => ?_
    have := hG (-ε) (fun _ => ε) (fun _ => 0) (by linarith) (fun ℓ => by simpa [en_zero] using hε)
    have e : α * -ε + ∑ ℓ : Fin (k + 1), ν ℓ * ε + ∑ ℓ : Fin (k + 1), μ ℓ ⬝ᵥ (0 : Fin (q ℓ) → ℝ)
        = ε * (-α + ∑ ℓ, ν ℓ) := by
      simp [← Finset.sum_mul]; ring
    linarith
  have hle : ∀ (s : ℝ) (t : Fin (k + 1) → ℝ) (y : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ),
      s ≤ 0 → (∀ ℓ, euclidNorm (y ℓ) ≤ t ℓ) →
        α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ ≤ 0 := by
    intro s t y hs hy
    refine lim_zero _ (α - ∑ ℓ, ν ℓ) fun ε hε => ?_
    have := ha (s - ε) (fun ℓ => t ℓ + ε) y (by linarith) (fun ℓ => by linarith [hy ℓ])
    have e : α * (s - ε) + ∑ ℓ, ν ℓ * (t ℓ + ε) + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ
        = (α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ) - ε * (α - ∑ ℓ, ν ℓ) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]; ring
    linarith
  have hα : 0 ≤ α := by
    have := hle (-1) 0 (fun _ => 0) (by norm_num) (fun ℓ => by simp [en_zero])
    simp at this
    linarith
  have hsingle : ∀ ℓ (t0 : ℝ) (y0 : Fin (q ℓ) → ℝ), euclidNorm y0 ≤ t0 →
      ν ℓ * t0 + μ ℓ ⬝ᵥ y0 ≤ 0 := by
    intro ℓ t0 y0 hy0
    have := hle 0 (Pi.single ℓ t0) (Pi.single ℓ y0) le_rfl (fun ℓ' => by
      by_cases h : ℓ' = ℓ
      · subst h; simpa using hy0
      · simp [Pi.single_eq_of_ne h, en_zero])
    have e1 : ∑ ℓ', ν ℓ' * (Pi.single ℓ t0 : Fin (k + 1) → ℝ) ℓ' = ν ℓ * t0 := by
      rw [Finset.sum_eq_single ℓ]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    have e2 : ∑ ℓ', μ ℓ' ⬝ᵥ (Pi.single ℓ y0 : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ) ℓ'
        = μ ℓ ⬝ᵥ y0 := by
      rw [Finset.sum_eq_single ℓ]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    rw [e1, e2] at this
    linarith
  refine ⟨hu, hα, fun ℓ => ?_⟩
  have h1 := hsingle ℓ 1 0 (by simp [en_zero])
  have h2 := hsingle ℓ (euclidNorm (μ ℓ)) (μ ℓ) le_rfl
  have hdot : μ ℓ ⬝ᵥ μ ℓ = euclidNorm (μ ℓ) ^ 2 := by
    rw [en_sq]; simp [dotProduct, sq]
  rw [hdot] at h2
  simp at h1
  rcases (en_nonneg (μ ℓ)).eq_or_lt with h | h
  · rw [← h]; linarith
  · nlinarith


theorem cqp_core {N p k : ℕ} (P : CQPData N p k)
    (hstrict : ∃ z, P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) < P.c ℓ ⬝ᵥ z - P.d ℓ)
    (hbdd : BddBelow (P.primalObj '' P.primalFeas)) :
    ∃ v : ℝ, IsGLB (P.primalObj '' P.primalFeas) v ∧ IsGreatest (P.dualObj '' P.dualFeas) v := by
  classical
  obtain ⟨z0, hz0R, hz0⟩ := hstrict
  have hne : (P.primalObj '' P.primalFeas).Nonempty :=
    ⟨_, z0, ⟨hz0R, fun ℓ => (hz0 ℓ).le⟩, rfl⟩
  obtain ⟨v, hglb⟩ : ∃ v, IsGLB (P.primalObj '' P.primalFeas) v := ⟨_, isGLB_csInf hne hbdd⟩
  have key : ∃ w ∈ P.dualFeas, v ≤ P.dualObj w := by
    have hdisj : Disjoint (GSet P.q) (PhiMap P v '' {z | P.R *ᵥ z = P.r}) := by
      rw [Set.disjoint_left]
      rintro g ⟨hg1, hg2⟩ ⟨z, hz, rfl⟩
      have hfeas : z ∈ P.primalFeas := ⟨hz, fun ℓ => (hg2 ℓ).le⟩
      have := hglb.1 ⟨z, hfeas, rfl⟩
      have h1 : P.primalObj z - v < 0 := hg1
      linarith
    obtain ⟨f, u, hfG, hfT⟩ :=
      geometric_hahn_banach_open (GSet_convex P.q) (GSet_isOpen P.q) (T_convex P v) hdisj
    obtain ⟨α, ν, μ, hf⟩ := expand P.q f.toLinearMap
    have hG : ∀ (s : ℝ) (t : Fin (k + 1) → ℝ) (y : (ℓ : Fin (k + 1)) → Fin (P.q ℓ) → ℝ),
        s < 0 → (∀ ℓ, euclidNorm (y ℓ) < t ℓ) →
          α * s + ∑ ℓ, ν ℓ * t ℓ + ∑ ℓ, μ ℓ ⬝ᵥ y ℓ < u := by
      intro s t y hs hy
      rw [← hf]
      exact hfG _ ⟨hs, hy⟩
    obtain ⟨hu, hα, hμν⟩ := sep_consequences P.q α ν μ u hG
    have hT : ∀ z, P.R *ᵥ z = P.r →
        u ≤ α * (P.primalObj z - v) + ∑ ℓ, ν ℓ * (P.c ℓ ⬝ᵥ z - P.d ℓ)
          + ∑ ℓ, μ ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ) := by
      intro z hz
      have := hfT _ ⟨z, hz, rfl⟩
      rw [← hf] at *
      exact this
    rcases hα.eq_or_lt with h0 | hpos
    · exfalso
      subst h0
      have h1 := hG (-1) (fun ℓ => P.c ℓ ⬝ᵥ z0 - P.d ℓ) (fun ℓ => P.A ℓ *ᵥ z0 - P.b ℓ)
        (by norm_num) hz0
      have h2 := hT z0 hz0R
      simp only [zero_mul] at h1 h2
      linarith
    · set a : Fin N → ℝ := α • P.e + ∑ ℓ, ν ℓ • P.c ℓ + ∑ ℓ, (P.A ℓ)ᵀ *ᵥ μ ℓ with ha
      set κ : ℝ := α * (P.φ - v) - ∑ ℓ, ν ℓ * P.d ℓ - ∑ ℓ, μ ℓ ⬝ᵥ P.b ℓ with hκ
      have hid : ∀ z, α * (P.primalObj z - v) + ∑ ℓ, ν ℓ * (P.c ℓ ⬝ᵥ z - P.d ℓ)
          + ∑ ℓ, μ ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ) = a ⬝ᵥ z + κ := by
        intro z
        have h1 : a ⬝ᵥ z = α * (P.e ⬝ᵥ z) + ∑ ℓ, ν ℓ * (P.c ℓ ⬝ᵥ z)
            + ∑ ℓ, μ ℓ ⬝ᵥ (P.A ℓ *ᵥ z) := by
          simp only [ha, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul,
            Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        have h2 : ∑ ℓ, ν ℓ * (P.c ℓ ⬝ᵥ z - P.d ℓ)
            = ∑ ℓ, ν ℓ * (P.c ℓ ⬝ᵥ z) - ∑ ℓ, ν ℓ * P.d ℓ := by
          simp [mul_sub, Finset.sum_sub_distrib]
        have h3 : ∑ ℓ, μ ℓ ⬝ᵥ (P.A ℓ *ᵥ z - P.b ℓ)
            = ∑ ℓ, μ ℓ ⬝ᵥ (P.A ℓ *ᵥ z) - ∑ ℓ, μ ℓ ⬝ᵥ P.b ℓ := by
          simp [dotProduct_sub, Finset.sum_sub_distrib]
        rw [h1, h2, h3, hκ]
        unfold primalObj
        ring
      have hnn : ∀ z, P.R *ᵥ z = P.r → 0 ≤ a ⬝ᵥ z + κ := fun z hz => by
        rw [← hid]; linarith [hT z hz]
      obtain ⟨ρ, hρ⟩ := la_range P.R P.r z0 hz0R a κ hnn
      have hz0' := hnn z0 hz0R
      have haz : a ⬝ᵥ z0 = P.r ⬝ᵥ ρ := by
        rw [hρ, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hz0R, dotProduct_comm]
      have hαne : α ≠ 0 := hpos.ne'
      have hαi : 0 < α⁻¹ := inv_pos.2 hpos
      refine ⟨(α⁻¹ • ρ, fun ℓ => (-α⁻¹) • μ ℓ, fun ℓ => -α⁻¹ * ν ℓ), ⟨?_, ?_⟩, ?_⟩
      · -- equation
        ext j
        have hj := congrFun hρ j
        simp only [ha, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at hj
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec_smul]
        rw [Finset.sum_add_distrib]
        have s1 : ∑ x, -α⁻¹ * ν x * P.c x j = -α⁻¹ * ∑ x, ν x * P.c x j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        have s2 : ∑ x, -α⁻¹ * ((P.A x)ᵀ *ᵥ μ x) j = -α⁻¹ * ∑ x, ((P.A x)ᵀ *ᵥ μ x) j := by
          rw [Finset.mul_sum]
        have e0 : P.e j = α⁻¹ * (α * P.e j) := by field_simp
        rw [s1, s2, e0]
        linear_combination (-α⁻¹) * hj
      · intro ℓ
        show euclidNorm ((-α⁻¹) • μ ℓ) ≤ -α⁻¹ * ν ℓ
        rw [en_smul, abs_neg, abs_of_pos hαi]
        have := hμν ℓ
        nlinarith
      · show v ≤ P.r ⬝ᵥ (α⁻¹ • ρ) + ∑ ℓ, (P.d ℓ * (-α⁻¹ * ν ℓ) + P.b ℓ ⬝ᵥ ((-α⁻¹) • μ ℓ)) + P.φ
        have e1 : ∑ ℓ, (P.d ℓ * (-α⁻¹ * ν ℓ) + P.b ℓ ⬝ᵥ ((-α⁻¹) • μ ℓ))
            = -α⁻¹ * (∑ ℓ, ν ℓ * P.d ℓ + ∑ ℓ, μ ℓ ⬝ᵥ P.b ℓ) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [dotProduct_smul, dotProduct_comm (P.b ℓ)]
          simp only [smul_eq_mul]; ring
        have hk : 0 ≤ P.r ⬝ᵥ ρ + κ := by rw [haz] at hz0'; exact hz0'
        have h := mul_nonneg hαi.le hk
        have h2 : α⁻¹ * (P.r ⬝ᵥ ρ + κ) = α⁻¹ * (P.r ⬝ᵥ ρ)
            + -α⁻¹ * (∑ ℓ, ν ℓ * P.d ℓ + ∑ ℓ, μ ℓ ⬝ᵥ P.b ℓ) + P.φ - v := by
          rw [hκ]; field_simp; ring
        rw [dotProduct_smul, e1, smul_eq_mul]
        linarith
  obtain ⟨w, hw, hvw⟩ := key
  refine ⟨v, hglb, ⟨w, hw, le_antisymm ?_ hvw⟩, ?_⟩
  · exact hglb.2 (fun x ⟨z, hz, hzx⟩ => hzx ▸ weak_dual P z hz w hw)
  · rintro _ ⟨w', hw', rfl⟩
    exact hglb.2 (fun x ⟨z, hz, hzx⟩ => hzx ▸ weak_dual P z hz w' hw')

end RobustUncLP.Ellipsoidal

open RobustUncLP.Ellipsoidal
open Matrix CQPData

theorem solution {N p k : ℕ} (P : CQPData N p k)
    (hstrict : ∃ z, P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) < P.c ℓ ⬝ᵥ z - P.d ℓ)
    (hbdd : BddBelow (P.primalObj '' P.primalFeas)) :
    ∃ v : ℝ, IsGLB (P.primalObj '' P.primalFeas) v ∧ IsGreatest (P.dualObj '' P.dualFeas) v := by
  exact cqp_core P hstrict hbdd
