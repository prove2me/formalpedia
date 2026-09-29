-- Prove2me | solution 1 for RobustSDP.FullPert.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:44:29.096915+00:00
-- url     : https://prove2.me/submissions/e0915e02-7f85-4a47-b836-275984d92f39

import Mathlib
import Definitions.Def_RobustSDP_FullPert_Model

open Matrix
open scoped Matrix.Norms.L2Operator


namespace RobustSDP.FullPert

/-- The L2 operator norm is attained on a vector (or the matrix norm is zero). -/
lemma wp_attain {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (hD : 0 < ‖D‖) :
    ∃ u : EuclideanSpace ℝ (Fin p), ‖u‖ = 1 ∧
      ‖(WithLp.toLp 2 (D *ᵥ WithLp.ofLp u) : EuclideanSpace ℝ (Fin q))‖ = ‖D‖ := by
  set T : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    (toEuclideanLin (𝕜 := ℝ) (m := Fin q) (n := Fin p)).trans LinearMap.toContinuousLinearMap D
    with hT
  have hTx : ∀ x, T x = WithLp.toLp 2 (D *ᵥ WithLp.ofLp x) := fun x => rfl
  have hDT : ‖D‖ = ‖T‖ := rfl
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1).Nonempty
  · obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin p)) 1).exists_isMaxOn hne
      (continuous_norm.comp T.continuous).continuousOn
    have hu1 : ‖u‖ = 1 := by simpa using hu
    refine ⟨u, hu1, ?_⟩
    rw [← hTx]
    apply le_antisymm
    · rw [hDT]; simpa [hu1] using T.le_opNorm u
    · rw [hDT]
      refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1 := by
          simp [norm_smul, hxn.ne']
        have h0 : ‖T (‖x‖⁻¹ • x)‖ ≤ ‖T u‖ := hmax hmem
        rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hxn] at h0
        have this := h0
        linarith [mul_comm ‖x‖ ‖T u‖]
  · exfalso
    have : ‖T‖ ≤ 0 := by
      refine T.opNorm_le_bound le_rfl fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · exfalso; apply hne
        have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, hxn.ne']⟩
    rw [← hDT] at this; linarith

theorem well_posed_core {p q : ℕ} (D : Matrix (Fin q) (Fin p) ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ → (1 - D * Δ).det ≠ 0) ↔ ‖D‖ < ρ⁻¹ := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hσ : 0 < ‖D‖ := lt_of_lt_of_le (inv_pos.mpr hρ) hc
    obtain ⟨u, hu1, huD⟩ := wp_attain D hσ
    set σ := ‖D‖ with hσdef
    set w : Fin q → ℝ := D *ᵥ WithLp.ofLp u with hw
    have hww : w ⬝ᵥ w = σ ^ 2 := by
      rw [← huD, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp
    set Δ : Matrix (Fin p) (Fin q) ℝ := (σ ^ 2)⁻¹ • vecMulVec (WithLp.ofLp u) w with hΔ
    have hnorm : ‖Δ‖ ≤ ρ := by
      have h1 : ‖Δ‖ ≤ σ⁻¹ := by
        rw [l2_opNorm_def]
        refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hσ.le) fun x => ?_
        change ‖(WithLp.toLp 2 (Δ *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin p))‖ ≤ σ⁻¹ * ‖x‖
        have he : (WithLp.toLp 2 (Δ *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin p)) =
            ((σ ^ 2)⁻¹ * (w ⬝ᵥ WithLp.ofLp x)) • u := by
          rw [hΔ, smul_mulVec, vecMulVec_mulVec]
          ext i
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [he, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
        have hcs : |w ⬝ᵥ WithLp.ofLp x| ≤ σ * ‖x‖ := by
          have := abs_real_inner_le_norm (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q)) x
          rw [EuclideanSpace.inner_eq_star_dotProduct] at this
          simp only [star_trivial] at this
          rw [dotProduct_comm]
          have hwn : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin q))‖ = σ := huD
          rw [hwn] at this
          simpa using this
        calc (σ ^ 2)⁻¹ * |w ⬝ᵥ WithLp.ofLp x| ≤ (σ ^ 2)⁻¹ * (σ * ‖x‖) :=
              mul_le_mul_of_nonneg_left hcs (by positivity)
          _ = σ⁻¹ * ‖x‖ := by field_simp
      have h2 : σ⁻¹ ≤ ρ := by
        rw [inv_le_comm₀ hσ hρ]; exact hc
      linarith
    apply h Δ hnorm
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨w, ?_, ?_⟩
    · intro h0
      have : σ ^ 2 = 0 := by rw [← hww, h0]; simp
      exact hσ.ne' (by simpa using this)
    · rw [sub_mulVec, one_mulVec, hΔ, Matrix.mul_smul, mul_vecMulVec, smul_mulVec, vecMulVec_mulVec, ← hw,
        hww]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, Pi.zero_apply]
      field_simp
      ring
  · intro hD Δ hΔ
    have h1 : ‖D * Δ‖ < 1 := by
      calc ‖D * Δ‖ ≤ ‖D‖ * ‖Δ‖ := l2_opNorm_mul D Δ
        _ ≤ ‖D‖ * ρ := mul_le_mul_of_nonneg_left hΔ (norm_nonneg _)
        _ < ρ⁻¹ * ρ := mul_lt_mul_of_pos_right hD hρ
        _ = 1 := inv_mul_cancel₀ hρ.ne'
    have hu : IsUnit (1 - D * Δ) := (Units.oneSub (D * Δ) h1).isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero


/-- quadratic form -/
def qfm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ := z ⬝ᵥ (A *ᵥ z)

lemma qfm_add_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z w : ι → ℝ) (t : ℝ) :
    qfm A (z + t • w) = qfm A z + t * (z ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ z)) + t ^ 2 * qfm A w := by
  unfold qfm
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

lemma slemma_pair {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ)
    (h : ∀ z, 0 ≤ qfm B z → 0 ≤ qfm A z) (z w : ι → ℝ) (hz : 0 < qfm B z) (hw : qfm B w < 0) :
    qfm A z * qfm B w ≤ qfm A w * qfm B z := by
  set α := qfm B z
  set γ := qfm B w
  set b := z ⬝ᵥ (B *ᵥ w) + w ⬝ᵥ (B *ᵥ z)
  set fz := qfm A z
  set fw := qfm A w
  set c := z ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ z)
  have hdisc : 0 ≤ b ^ 2 - 4 * α * γ := by nlinarith [sq_nonneg b]
  set d := Real.sqrt (b ^ 2 - 4 * α * γ)
  have hd2 : d ^ 2 = b ^ 2 - 4 * α * γ := Real.sq_sqrt hdisc
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hdb : b < d := by nlinarith [sq_nonneg (b - d), sq_nonneg (b + d)]
  have hdb' : -b < d := by nlinarith [sq_nonneg (b - d), sq_nonneg (b + d)]
  have hγ2 : 2 * γ ≠ 0 := by linarith
  set t₁ := (-b + d) / (2 * γ)
  set t₂ := (-b - d) / (2 * γ)
  have ht₁ : t₁ < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have ht₂ : 0 < t₂ := div_pos_of_neg_of_neg (by linarith) (by linarith)
  have hr₁ : α + t₁ * b + t₁ ^ 2 * γ = 0 := by
    have : t₁ * (2 * γ) = -b + d := div_mul_cancel₀ _ hγ2
    have hh : 4 * γ * (α + t₁ * b + t₁ ^ 2 * γ) = 0 := by nlinarith
    have : (4 * γ) ≠ 0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_left this
  have hr₂ : α + t₂ * b + t₂ ^ 2 * γ = 0 := by
    have : t₂ * (2 * γ) = -b - d := div_mul_cancel₀ _ hγ2
    have hh : 4 * γ * (α + t₂ * b + t₂ ^ 2 * γ) = 0 := by nlinarith
    have : (4 * γ) ≠ 0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_left this
  have hA₁ : 0 ≤ fz + t₁ * c + t₁ ^ 2 * fw := by
    have := h (z + t₁ • w) (by rw [qfm_add_smul]; linarith)
    rwa [qfm_add_smul] at this
  have hA₂ : 0 ≤ fz + t₂ * c + t₂ ^ 2 * fw := by
    have := h (z + t₂ • w) (by rw [qfm_add_smul]; linarith)
    rwa [qfm_add_smul] at this
  set P := α * c - fz * b
  set K := α * fw - fz * γ
  have e₁ : 0 ≤ t₁ * (P + t₁ * K) := by
    have : t₁ * (P + t₁ * K) = α * (fz + t₁ * c + t₁ ^ 2 * fw) - fz * (α + t₁ * b + t₁ ^ 2 * γ) := by
      ring
    rw [this, hr₁]; nlinarith
  have e₂ : 0 ≤ t₂ * (P + t₂ * K) := by
    have : t₂ * (P + t₂ * K) = α * (fz + t₂ * c + t₂ ^ 2 * fw) - fz * (α + t₂ * b + t₂ ^ 2 * γ) := by
      ring
    rw [this, hr₂]; nlinarith
  have f₁ : P + t₁ * K ≤ 0 := by
    by_contra hc; push_neg at hc; nlinarith
  have f₂ : 0 ≤ P + t₂ * K := by
    by_contra hc; push_neg at hc; nlinarith
  have hK : 0 ≤ K := by
    by_contra hc; push_neg at hc; nlinarith
  linarith

lemma slemma {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (hs : ∃ z, 0 < qfm B z)
    (h : ∀ z, 0 ≤ qfm B z → 0 ≤ qfm A z) : ∃ τ : ℝ, ∀ z, τ * qfm B z ≤ qfm A z := by
  obtain ⟨z0, hz0⟩ := hs
  set S : Set ℝ := {r | ∃ w, qfm B w < 0 ∧ r = qfm A w / qfm B w}
  by_cases hS : S.Nonempty
  · have hbd : ∀ z, 0 < qfm B z → ∀ r ∈ S, r ≤ qfm A z / qfm B z := by
      intro z hz r ⟨w, hw, hr⟩
      rw [hr]
      have hp := slemma_pair A B h z w hz hw
      rw [show qfm A w / qfm B w = (-qfm A w) / (-qfm B w) by rw [neg_div_neg_eq],
        div_le_div_iff₀ (by linarith) hz]
      nlinarith
    have hB : BddAbove S := ⟨qfm A z0 / qfm B z0, fun r hr => hbd z0 hz0 r hr⟩
    refine ⟨sSup S, fun z => ?_⟩
    rcases lt_trichotomy (qfm B z) 0 with hneg | hzero | hpos
    · have hmem : qfm A z / qfm B z ∈ S := ⟨z, hneg, rfl⟩
      have := le_csSup hB hmem
      exact (div_le_iff_of_neg hneg).mp this
    · rw [hzero, mul_zero]; exact h z hzero.ge
    · have := csSup_le hS (hbd z hpos)
      exact (le_div_iff₀ hpos).mp this
  · refine ⟨0, fun z => ?_⟩
    rw [zero_mul]
    apply h
    by_contra hc; push_neg at hc
    exact hS ⟨_, z, hc, rfl⟩


lemma nsq {a : ℕ} (v : Fin a → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin a))‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]; simp

lemma nmulVec {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ) :
    ‖(WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℝ (Fin a))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin b))‖ :=
  l2_opNorm_mulVec M (WithLp.toLp 2 v)

lemma nvecMulVec {a b : ℕ} (u : Fin a → ℝ) (w : Fin b → ℝ) :
    ‖vecMulVec u w‖ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin a))‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin b))‖ := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  change ‖(WithLp.toLp 2 (vecMulVec u w *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin a))‖ ≤ _
  have he : (WithLp.toLp 2 (vecMulVec u w *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin a)) =
      (w ⬝ᵥ WithLp.ofLp x) • (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin a)) := by
    rw [vecMulVec_mulVec]; ext i; simp [mul_comm]
  rw [he, norm_smul, Real.norm_eq_abs]
  have hcs : |w ⬝ᵥ WithLp.ofLp x| ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin b))‖ * ‖x‖ := by
    have := abs_real_inner_le_norm (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin b)) x
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [star_trivial] at this
    rw [dotProduct_comm]
    simpa using this
  have h0 := norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin a))
  nlinarith

lemma ntrans {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ‖Mᵀ‖ = ‖M‖ := by
  simpa using l2_opNorm_conjTranspose M

lemma dm {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma dot_self_nonneg' {a : ℕ} (v : Fin a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma elim_dot {a b : ℕ} (x z : Fin a → ℝ) (y w : Fin b → ℝ) :
    (Sum.elim x y : Fin a ⊕ Fin b → ℝ) ⬝ᵥ Sum.elim z w = x ⬝ᵥ z + y ⬝ᵥ w := by
  simp [dotProduct, Fintype.sum_sum_type]

lemma qA {n q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin q) (Fin n) ℝ)
    (ξ : Fin n → ℝ) (η : Fin q → ℝ) :
    qfm (fromBlocks F Rᵀ R 0) (Sum.elim ξ η) = ξ ⬝ᵥ (F *ᵥ ξ) + 2 * (η ⬝ᵥ (R *ᵥ ξ)) := by
  unfold qfm
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, elim_dot, zero_mulVec,
    add_zero, dotProduct_add]
  rw [dm Rᵀ ξ η, transpose_transpose, dotProduct_comm (R *ᵥ ξ) η]
  ring

lemma qB {n p q : ℕ} (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (c : ℝ)
    (ξ : Fin n → ℝ) (η : Fin q → ℝ) :
    qfm (fromBlocks (L * Lᵀ) (L * Dᵀ) (D * Lᵀ) (D * Dᵀ - c • (1 : Matrix (Fin q) (Fin q) ℝ)))
        (Sum.elim ξ η) =
      (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η) ⬝ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η) - c * (η ⬝ᵥ η) := by
  unfold qfm
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, elim_dot,
    dotProduct_add, add_dotProduct, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul, ← mulVec_mulVec]
  rw [dm L ξ, dm L ξ, dm D η, dm D η, dotProduct_comm (Dᵀ *ᵥ η) (Lᵀ *ᵥ ξ)]
  ring

lemma gexp {n p q : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) (K : Matrix (Fin q) (Fin q) ℝ)
    (ξ : Fin n → ℝ) :
    ξ ⬝ᵥ ((F + L * Δ * K * R + Rᵀ * Kᵀ * Δᵀ * Lᵀ) *ᵥ ξ) =
      ξ ⬝ᵥ (F *ᵥ ξ) + 2 * ((Kᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ))) ⬝ᵥ (R *ᵥ ξ)) := by
  simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec]
  rw [dm L ξ, dm Δ, dm K, dm Rᵀ ξ, transpose_transpose,
    dotProduct_comm (R *ᵥ ξ)]
  ring

theorem core_rho {n p q : ℕ} (hq : 0 < q) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (hL : L ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (hD : ‖D‖ < ρ⁻¹) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ ρ →
        (1 - D * Δ).det ≠ 0 ∧
          (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosSemidef) ↔
      ∃ τ : ℝ, (fromBlocks (F - τ • (L * Lᵀ)) (Rᵀ - τ • (L * Dᵀ)) (R - τ • (D * Lᵀ))
          (τ • ((ρ ^ 2)⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ) - D * Dᵀ))).PosSemidef := by
  set c : ℝ := (ρ ^ 2)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set A := fromBlocks F Rᵀ R (0 : Matrix (Fin q) (Fin q) ℝ) with hA
  set B := fromBlocks (L * Lᵀ) (L * Dᵀ) (D * Lᵀ) (D * Dᵀ - c • (1 : Matrix (Fin q) (Fin q) ℝ))
    with hB
  have hM : ∀ τ : ℝ, fromBlocks (F - τ • (L * Lᵀ)) (Rᵀ - τ • (L * Dᵀ)) (R - τ • (D * Lᵀ))
      (τ • (c • (1 : Matrix (Fin q) (Fin q) ℝ) - D * Dᵀ)) = A - τ • B := by
    intro τ
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [hA, hB] <;> ring
  have hqM : ∀ τ v, qfm (A - τ • B) v = qfm A v - τ * qfm B v := by
    intro τ v
    unfold qfm
    rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hFt : Fᵀ = F := hF
  have hHerm : ∀ τ : ℝ, (A - τ • B).IsHermitian := by
    intro τ
    rw [← hM τ]
    refine IsHermitian.fromBlocks ?_ ?_ ?_
    · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul, hFt]
    · simp [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul]
    · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul,
        transpose_smul]
  have hsplit : ∀ v : Fin n ⊕ Fin q → ℝ, v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) :=
    fun v => (Sum.elim_comp_inl_inr v).symm
  -- key relation between η and Δ
  have hrel : ∀ (Δ : Matrix (Fin p) (Fin q) ℝ), (1 - D * Δ).det ≠ 0 → ∀ (ξ : Fin n → ℝ) (η : Fin q → ℝ),
      (η = ((1 - D * Δ)⁻¹)ᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ)) ↔ η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ + Dᵀ *ᵥ η)) := by
    intro Δ hdet ξ η
    have hu : IsUnit (1 - D * Δ).det := isUnit_iff_ne_zero.mpr hdet
    have h1 : ((1 - D * Δ)⁻¹)ᵀ * (1 - D * Δ)ᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
    have h2 : (1 - D * Δ)ᵀ * ((1 - D * Δ)⁻¹)ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hu, transpose_one]
    have h3 : ∀ y, (1 - D * Δ)ᵀ *ᵥ y = y - Δᵀ *ᵥ (Dᵀ *ᵥ y) := by
      intro y
      rw [transpose_sub, transpose_one, transpose_mul, sub_mulVec, one_mulVec, mulVec_mulVec]
    rw [mulVec_add]
    constructor
    · intro he
      have : (1 - D * Δ)ᵀ *ᵥ η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ) := by
        rw [he, mulVec_mulVec, h2, one_mulVec]
      rw [h3] at this
      rw [← this]; abel
    · intro he
      have : (1 - D * Δ)ᵀ *ᵥ η = Δᵀ *ᵥ (Lᵀ *ᵥ ξ) := by
        rw [h3]; nth_rewrite 1 [he]; abel
      rw [← this, mulVec_mulVec, h1, one_mulVec]
  constructor
  · intro h8
    have hs : ∃ z, 0 < qfm B z := by
      obtain ⟨i, j, hij⟩ : ∃ i j, L i j ≠ 0 := by
        by_contra hcon; push_neg at hcon
        exact hL (Matrix.ext hcon)
      refine ⟨Sum.elim (Pi.single i 1) 0, ?_⟩
      rw [hB, qB]
      simp only [mulVec_zero, add_zero, dotProduct_zero, mul_zero, sub_zero]
      set a := Lᵀ *ᵥ Pi.single i 1
      have ha : a j = L i j := by simp [a]
      have : a j * a j ≤ a ⬝ᵥ a :=
        Finset.single_le_sum (f := fun k => a k * a k) (fun k _ => mul_self_nonneg (a k))
          (Finset.mem_univ j)
      have : 0 < a j * a j := by rw [ha]; exact mul_self_pos.mpr hij
      linarith
    have hyp : ∀ z, 0 ≤ qfm B z → 0 ≤ qfm A z := by
      intro v hv
      rw [hsplit v] at hv ⊢
      set ξ := v ∘ Sum.inl
      set η := v ∘ Sum.inr
      rw [hB, qB] at hv
      rw [hA, qA]
      set b := Lᵀ *ᵥ ξ + Dᵀ *ᵥ η with hbdef
      set Δ : Matrix (Fin p) (Fin q) ℝ := (b ⬝ᵥ b)⁻¹ • vecMulVec b η with hΔ
      have hηη := dot_self_nonneg' η
      have hbb := dot_self_nonneg' b
      have hΔb : η = Δᵀ *ᵥ b := by
        by_cases hb : b ⬝ᵥ b = 0
        · have : η ⬝ᵥ η = 0 := by nlinarith
          have hη0 : η = 0 := dotProduct_self_eq_zero.mp this
          rw [hΔ, hb, hη0]; simp
        · rw [hΔ, transpose_smul, transpose_vecMulVec, smul_mulVec, vecMulVec_mulVec]
          ext k
          simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
            MulOpposite.unop_op]
          field_simp
      have hΔn : ‖Δ‖ ≤ ρ := by
        by_cases hb : b ⬝ᵥ b = 0
        · rw [hΔ, hb]; simp [hρ.le]
        · have hbpos : 0 < b ⬝ᵥ b := lt_of_le_of_ne hbb (Ne.symm hb)
          have h1 := nvecMulVec b η
          have hnb := nsq b
          have hnη := nsq η
          set nb := ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin p))‖
          set nη := ‖(WithLp.toLp 2 η : EuclideanSpace ℝ (Fin q))‖
          have hnb0 : 0 ≤ nb := norm_nonneg _
          have hnη0 : 0 ≤ nη := norm_nonneg _
          have hnbpos : 0 < nb := by
            rcases hnb0.lt_or_eq with h | h
            · exact h
            · exfalso; rw [← h] at hnb; linarith
          have hcη : c * nη ^ 2 ≤ nb ^ 2 := by rw [hnb, hnη]; linarith
          have hρc : ρ ^ 2 * c = 1 := by rw [hc]; field_simp
          have hηb : nη ≤ ρ * nb := by
            have : nη ^ 2 ≤ (ρ * nb) ^ 2 := by
              have := mul_le_mul_of_nonneg_left hcη (sq_nonneg ρ)
              nlinarith
            have hρnb : 0 ≤ ρ * nb := by positivity
            nlinarith
          have hsm : ‖Δ‖ ≤ (b ⬝ᵥ b)⁻¹ * (nb * nη) := by
            rw [hΔ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
            exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hbpos.le)
          rw [← hnb] at hsm
          calc ‖Δ‖ ≤ (nb ^ 2)⁻¹ * (nb * nη) := hsm
            _ ≤ (nb ^ 2)⁻¹ * (nb * (ρ * nb)) := by gcongr
            _ = ρ := by field_simp
      obtain ⟨hdet, hpsd⟩ := h8 Δ hΔn
      have hq' := hpsd.dotProduct_mulVec_nonneg ξ
      rw [star_trivial, gexp] at hq'
      have heq : η = ((1 - D * Δ)⁻¹)ᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ)) := (hrel Δ hdet ξ η).mpr hΔb
      rw [← heq] at hq'
      exact hq'
    obtain ⟨τ, hτ⟩ := slemma A B hs hyp
    refine ⟨τ, ?_⟩
    rw [hM τ]
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hHerm τ) fun v => ?_
    rw [star_trivial]
    show 0 ≤ qfm (A - τ • B) v
    rw [hqM]
    linarith [hτ v]
  · rintro ⟨τ, hpsd⟩ Δ hΔ
    rw [hM τ] at hpsd
    have hdet := (well_posed_core D ρ hρ).mpr hD Δ hΔ
    refine ⟨hdet, ?_⟩
    have hquad : ∀ v, 0 ≤ qfm A v - τ * qfm B v := by
      intro v
      rw [← hqM]
      have := hpsd.dotProduct_mulVec_nonneg v
      rwa [star_trivial] at this
    have hcρ : c = ρ⁻¹ ^ 2 := by rw [hc, inv_pow]
    have hτ0 : 0 ≤ τ := by
      set e : Fin q → ℝ := Pi.single ⟨0, hq⟩ 1 with he
      have h1 := hquad (Sum.elim 0 e)
      rw [hA, qA, hB, qB] at h1
      simp only [mulVec_zero, zero_add, dotProduct_zero, mul_zero, add_zero] at h1
      have hee : e ⬝ᵥ e = 1 := by simp [e]
      have hn := nmulVec Dᵀ e
      rw [ntrans] at hn
      have hsq := nsq (Dᵀ *ᵥ e)
      have hse := nsq e
      rw [hee] at hse
      have hne0 := norm_nonneg (WithLp.toLp 2 e : EuclideanSpace ℝ (Fin q))
      have hne : ‖(WithLp.toLp 2 e : EuclideanSpace ℝ (Fin q))‖ = 1 := by nlinarith
      rw [hne, mul_one] at hn
      have hs0 := norm_nonneg (WithLp.toLp 2 (Dᵀ *ᵥ e) : EuclideanSpace ℝ (Fin p))
      have hlt : (Dᵀ *ᵥ e) ⬝ᵥ (Dᵀ *ᵥ e) < c := by
        rw [← hsq, hcρ]
        have := lt_of_le_of_lt hn hD
        exact pow_lt_pow_left₀ this hs0 two_ne_zero
      rw [hee] at h1
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos (neg_pos.mpr hneg) (sub_pos.mpr hlt)]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ξ => ?_
    · simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_mul, hFt,
        Matrix.mul_assoc]
      abel
    · rw [star_trivial, gexp]
      set η := ((1 - D * Δ)⁻¹)ᵀ *ᵥ (Δᵀ *ᵥ (Lᵀ *ᵥ ξ)) with hη
      have hb := (hrel Δ hdet ξ η).mp rfl
      set b := Lᵀ *ᵥ ξ + Dᵀ *ᵥ η with hbdef
      have hn := nmulVec Δᵀ b
      rw [ntrans, ← hb] at hn
      have hnη := nsq η
      have hnb := nsq b
      set nb := ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin p))‖
      set nη := ‖(WithLp.toLp 2 η : EuclideanSpace ℝ (Fin q))‖
      have hnb0 : 0 ≤ nb := norm_nonneg _
      have hnη0 : 0 ≤ nη := norm_nonneg _
      have h2 : nη ≤ ρ * nb := le_trans hn (mul_le_mul_of_nonneg_right hΔ hnb0)
      have h3 : nη ^ 2 ≤ (ρ * nb) ^ 2 := pow_le_pow_left₀ hnη0 h2 2
      have hρc : ρ ^ 2 * c = 1 := by rw [hc]; field_simp
      have hBv : 0 ≤ qfm B (Sum.elim ξ η) := by
        rw [hB, qB, ← hnη, ← hnb]
        have : c * nη ^ 2 ≤ c * (ρ * nb) ^ 2 := mul_le_mul_of_nonneg_left h3 hc0.le
        nlinarith
      have hAv := hquad (Sum.elim ξ η)
      rw [hA, qA] at hAv
      nlinarith [mul_nonneg hτ0 hBv]


theorem lemma_3_1_core {n p q : ℕ} (hq : 0 < q) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (hL : L ≠ 0) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧
          (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosSemidef) ↔
      (‖D‖ < 1 ∧ ∃ τ : ℝ,
        (fromBlocks (F - τ • (L * Lᵀ)) (Rᵀ - τ • (L * Dᵀ)) (R - τ • (D * Lᵀ))
          (τ • (1 - D * Dᵀ))).PosSemidef) := by
  have hsimp : ((1 : ℝ) ^ 2)⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ) = 1 := by simp
  constructor
  · intro h8
    have hD : ‖D‖ < 1 := by
      have := (well_posed_core D 1 one_pos).mp (fun Δ hΔ => (h8 Δ hΔ).1)
      simpa using this
    refine ⟨hD, ?_⟩
    obtain ⟨τ, hτ⟩ := (core_rho hq F hF L R D hL 1 one_pos (by simpa using hD)).mp h8
    rw [hsimp] at hτ
    exact ⟨τ, hτ⟩
  · rintro ⟨hD, τ, hτ⟩
    exact (core_rho hq F hF L R D hL 1 one_pos (by simpa using hD)).mpr ⟨τ, by rw [hsimp]; exact hτ⟩


theorem theorem_3_1_core {m n p q : ℕ} (hq : 0 < q)
    (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hFs : ∀ i, (Fs i).IsSymm)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (hL : L ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (hD : ‖D‖ < ρ⁻¹)
    (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs Rs L D ⊤ ρ ↔
      ∃ τ : ℝ, (sdpLMI (affineMap Fs x) (affineMap Rs x) L D ρ τ).PosSemidef := by
  have hFx : (affineMap Fs x).IsSymm := by
    have ht : ∀ i, (Fs i)ᵀ = Fs i := fun i => hFs i
    show (affineMap Fs x)ᵀ = affineMap Fs x
    simp [affineMap, transpose_add, transpose_sum, transpose_smul, ht]
  have hinv : ∀ Δ : Matrix (Fin p) (Fin q) ℝ, (1 - Δᵀ * Dᵀ)⁻¹ = ((1 - D * Δ)⁻¹)ᵀ := by
    intro Δ
    rw [transpose_nonsing_inv, transpose_sub, transpose_one, transpose_mul]
  unfold sdpLMI
  rw [← core_rho hq _ hFx L _ D hL ρ hρ hD]
  simp only [robustFeasibleSet, Set.mem_setOf_eq, Submodule.mem_top, true_implies, lfr, hinv]

end RobustSDP.FullPert

open RobustSDP.FullPert


theorem solution {m n p q : ℕ} (hq : 0 < q)
    (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hFs : ∀ i, (Fs i).IsSymm)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (hL : L ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (hD : ‖D‖ < ρ⁻¹)
    (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs Rs L D ⊤ ρ ↔
      ∃ τ : ℝ, (sdpLMI (affineMap Fs x) (affineMap Rs x) L D ρ τ).PosSemidef := by
  exact theorem_3_1_core hq Fs hFs Rs L D hL ρ hρ hD x
