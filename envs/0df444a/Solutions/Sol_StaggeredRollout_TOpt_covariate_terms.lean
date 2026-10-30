-- Prove2me | solution 1 for StaggeredRollout.TOpt.covariate_terms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:13:05.50775+00:00
-- url     : https://prove2.me/submissions/92af0ab6-ced3-4e9e-8790-15d525560c9f

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Quadratic

open Matrix StaggeredRollout.TOpt

private lemma dot_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- `Σ_{s,s'} (P_1)_{ss'} x_s y_{s'} = Σ_r (x_r - x̄)(y_r - ȳ)`. -/
private lemma pone_bilin (n : ℕ) (x y : Fin n → ℝ) :
    ∑ s, ∑ s', Pone n s s' * (x s * y s')
      = ∑ r, (x r - (n : ℝ)⁻¹ * ∑ s, x s) * (y r - (n : ℝ)⁻¹ * ∑ s, y s) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : ∀ s s' : Fin n, Pone n s s' = (if s = s' then 1 else 0) - (n : ℝ)⁻¹ := by
    intro s s'; simp [Pone, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  have lhs : ∑ s, ∑ s', Pone n s s' * (x s * y s')
      = ∑ s, x s * y s - (n : ℝ)⁻¹ * ((∑ s, x s) * (∑ s, y s)) := by
    simp only [hP, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
  rw [lhs]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- `x ⬝ (U (1+UᵀU)⁻¹ Uᵀ x) ≥ 0`. -/
private lemma B_psd {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) :
    (U * (1 + Uᵀ * U)⁻¹ * Uᵀ).PosSemidef := by
  have hM : (1 + Uᵀ * U : Matrix (Fin du) (Fin du) ℝ).PosSemidef := by
    have h2 := posSemidef_conjTranspose_mul_self U
    rw [conjTranspose_eq_transpose_of_trivial] at h2
    exact PosSemidef.one.add h2
  have := hM.inv.conjTranspose_mul_mul_same Uᵀ
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this

private lemma B_nonneg {N du : ℕ} (U : Matrix (Fin N) (Fin du) ℝ) (x : Fin N → ℝ) :
    0 ≤ x ⬝ᵥ ((U * (1 + Uᵀ * U)⁻¹ * Uᵀ) *ᵥ x) := by
  have := (B_psd U).dotProduct_mulVec_nonneg x
  simpa using this

/-- Centering identity for a bilinear form given by a matrix `B`. -/
private lemma quad_center (n N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ) (a : Fin n → Fin N → ℝ) :
    ∑ s, ∑ s', Pone n s s' * (a s ⬝ᵥ (B *ᵥ a s'))
      = ∑ r, (fun i => a r i - (n : ℝ)⁻¹ * ∑ s, a s i) ⬝ᵥ
          (B *ᵥ fun i => a r i - (n : ℝ)⁻¹ * ∑ s, a s i) := by
  have key : ∀ i i', ∑ s, ∑ s', Pone n s s' * (a s i * a s' i')
      = ∑ r, (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i') :=
    fun i i' => pone_bilin n (fun s => a s i) (fun s => a s i')
  simp only [dotProduct, mulVec, Finset.mul_sum]
  calc ∑ s, ∑ s', ∑ i, ∑ i', Pone n s s' * (a s i * (B i i' * a s' i'))
      = ∑ s, ∑ i, ∑ s', ∑ i', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ s', ∑ i', Pone n s s' * (a s i * (B i i' * a s' i')) := Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ i', ∑ s', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ i', ∑ s, ∑ s', Pone n s s' * (a s i * (B i i' * a s' i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ i', B i i' * ∑ s, ∑ s', Pone n s s' * (a s i * a s' i') := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ = ∑ i, ∑ i', ∑ r, (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ i, ∑ r, ∑ i', (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ i', (a r i - (n : ℝ)⁻¹ * ∑ s, a s i) *
          (B i i' * (a r i' - (n : ℝ)⁻¹ * ∑ s, a s i')) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

theorem solution (N T ℓ dx du : ℕ)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (z : Fin N → Fin T → ℝ) :
    (∀ j, 0 ≤ fXj ℓ X z j) ∧ (∀ j, 0 ≤ fUj ℓ U z j) ∧
    ((∃ μX : Fin dx → ℝ, ∀ t, Xᵀ *ᵥ (fun i => z i t) = μX) → ∀ j, fXj ℓ X z j = 0) ∧
    ((∃ μU : Fin du → ℝ, ∀ t, Uᵀ *ᵥ (fun i => z i t) = μU) → ∀ j, fUj ℓ U z j = 0) := by
  have hzc : ∀ j s, zCent ℓ z j s = (fun i => z i (win ℓ j s))
      - ((T - ℓ : ℕ) : ℝ)⁻¹ • ∑ s', (fun i => z i (win ℓ j s')) := by
    intro j s; funext i; simp [zCent, Finset.sum_apply]
  -- residual objective
  have hbdd : ∀ v : Fin N → ℝ,
      BddBelow (Set.range fun c : Fin dx → ℝ => (v - X *ᵥ c) ⬝ᵥ (v - X *ᵥ c)) := by
    intro v; refine ⟨0, ?_⟩; rintro _ ⟨c, rfl⟩; exact dot_self_nonneg' _
  have hinf_le : ∀ v : Fin N → ℝ,
      (⨅ c : Fin dx → ℝ, (v - X *ᵥ c) ⬝ᵥ (v - X *ᵥ c)) ≤ v ⬝ᵥ v := by
    intro v
    have := ciInf_le (hbdd v) 0
    simpa using this
  have hU_rewrite : ∀ j, fUj ℓ U z j = (N : ℝ)⁻¹ * ∑ r : Fin (T - ℓ),
      zCent ℓ z j r ⬝ᵥ ((U * (1 + Uᵀ * U)⁻¹ * Uᵀ) *ᵥ zCent ℓ z j r) := by
    intro j
    unfold fUj
    congr 1
    exact quad_center (T - ℓ) N _ (fun s i => z i (win ℓ j s))
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; unfold fXj
    apply mul_nonneg hNinv
    apply Finset.sum_nonneg; intro s _
    exact sub_nonneg.mpr (hinf_le _)
  · intro j
    rw [hU_rewrite]
    apply mul_nonneg hNinv
    apply Finset.sum_nonneg; intro s _
    exact B_nonneg U _
  · rintro ⟨μ, hμ⟩ j
    unfold fXj
    have horth : ∀ s : Fin (T - ℓ), Xᵀ *ᵥ zCent ℓ z j s = 0 := by
      intro s
      have hpos : 0 < T - ℓ := Fin.pos s
      have hn' : ((T - ℓ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [hzc, mulVec_sub, mulVec_smul, mulVec_sum]
      simp only [hμ, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn', one_smul, sub_self]
    have hinf : ∀ s : Fin (T - ℓ), (⨅ c : Fin dx → ℝ, (zCent ℓ z j s - X *ᵥ c) ⬝ᵥ
        (zCent ℓ z j s - X *ᵥ c)) = zCent ℓ z j s ⬝ᵥ zCent ℓ z j s := by
      intro s
      apply le_antisymm (hinf_le _)
      apply le_ciInf
      intro c
      have h0 : zCent ℓ z j s ⬝ᵥ (X *ᵥ c) = 0 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, horth s, zero_dotProduct]
      have h1 : (X *ᵥ c) ⬝ᵥ zCent ℓ z j s = 0 := by rw [dotProduct_comm, h0]
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, h0, h1]
      linarith [dot_self_nonneg' (X *ᵥ c)]
    simp only [hinf, sub_self, Finset.sum_const_zero, mul_zero]
  · rintro ⟨μ, hμ⟩ j
    unfold fUj
    set M := (1 + Uᵀ * U : Matrix (Fin du) (Fin du) ℝ)⁻¹
    have hconst : ∀ s s' : Fin (T - ℓ), (fun i => z i (win ℓ j s)) ⬝ᵥ
        ((U * M * Uᵀ) *ᵥ fun i => z i (win ℓ j s')) = μ ⬝ᵥ (M *ᵥ μ) := by
      intro s s'
      rw [← mulVec_mulVec, ← mulVec_mulVec, hμ, dotProduct_mulVec, ← mulVec_transpose, hμ]
    simp only [hconst]
    have hP0 : ∑ s : Fin (T - ℓ), ∑ s' : Fin (T - ℓ), Pone (T - ℓ) s s' = 0 := by
      rcases Nat.eq_zero_or_pos (T - ℓ) with h0 | hpos
      · exact Finset.sum_eq_zero (fun x _ => absurd x.isLt (by omega))
      have hn' : ((T - ℓ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      have h1 := pone_bilin (T - ℓ) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        inv_mul_cancel₀ hn', sub_self, mul_zero, Finset.sum_const_zero] at h1
      exact h1
    simp_rw [← Finset.sum_mul]
    rw [hP0, zero_mul, mul_zero]
