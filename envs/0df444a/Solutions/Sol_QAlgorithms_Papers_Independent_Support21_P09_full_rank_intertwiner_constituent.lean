-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P09.full_rank_intertwiner_constituent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:26:38.262516+00:00
-- url     : https://prove2.me/submissions/aca383fc-134d-4fa6-9dbc-459caa17dd43

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P09
open scoped BigOperators ComplexConjugate
open Matrix
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

theorem g66c_rep_inv {G : Type*} [Group G] {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Rep G I) (g : G) : psi g⁻¹ * psi g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem g66c_rep_inv' {G : Type*} [Group G] {I : Type*} [Fintype I] [DecidableEq I]
    (psi : Rep G I) (g : G) : psi g * psi g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- averaged equivariant right inverse -/
theorem g66c_avg {G : Type*} [Group G] [Fintype G] {d n : ℕ}
    (psi1 : Rep G (Fin d)) (psi2 : Rep G (Fin n))
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : MatrixIntertwines psi1 psi2 M)
    (N0 : Matrix (Fin n) (Fin d) ℂ) (hN0 : M * N0 = 1) :
    ∃ N : Matrix (Fin n) (Fin d) ℂ, M * N = 1 ∧ ∀ g, psi2 g * N = N * psi1 g := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨(1 / (Fintype.card G : ℂ)) • ∑ g, psi2 g * N0 * psi1 g⁻¹, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_sum]
    have : ∀ g, M * (psi2 g * N0 * psi1 g⁻¹) = 1 := by
      intro g
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hM g, Matrix.mul_assoc (psi1 g), hN0,
        Matrix.mul_one, g66c_rep_inv']
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div, inv_mul_cancel₀ hG, one_smul]
  · intro h
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [g66c_rep_inv, Matrix.mul_one]

theorem solution
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (psi1 : Rep G (Fin d)) (psi2 : Rep G (Fin n))
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : MatrixIntertwines psi1 psi2 M)
    (hrank : Function.Surjective M.mulVec) :
    d ≤ n ∧ ∃ c : ℕ, n = d + c ∧ ∃ chi : Rep G (Fin c),
    ∃ S : Matrix (Fin n) (Fin d ⊕ Fin c) ℂ,
    ∃ T : Matrix (Fin d ⊕ Fin c) (Fin n) ℂ,
      S * T = 1 ∧ T * S = 1 ∧
      ∀ g, T * psi2 g * S = Matrix.fromBlocks (psi1 g) 0 0 (chi g) := by
  obtain ⟨N0, hN0⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hrank
  have hdn : d ≤ n := by
    have h1 : (M * N0).rank ≤ M.rank := Matrix.rank_mul_le_left _ _
    rw [hN0, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := Matrix.rank_le_width M
    omega
  obtain ⟨N, hMN, hNint⟩ := g66c_avg psi1 psi2 M hM N0 hN0
  set c := n - d with hc
  have hker : Module.finrank ℂ (LinearMap.ker (Matrix.toLin' M)) = c := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    have hr : LinearMap.range (Matrix.toLin' M) = ⊤ := by
      rw [LinearMap.range_eq_top]; intro y
      obtain ⟨x, hx⟩ := hrank y
      exact ⟨x, by rw [Matrix.toLin'_apply]; exact hx⟩
    rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  let b := Module.finBasisOfFinrankEq ℂ _ hker
  let K : Matrix (Fin n) (Fin c) ℂ := Matrix.of fun i j => (b j : Fin n → ℂ) i
  have hKcol : ∀ x : Fin c → ℂ, K *ᵥ x = ((∑ j, x j • b j : LinearMap.ker (Matrix.toLin' M)) :
      Fin n → ℂ) := by
    intro x; ext i
    simp [K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
  have hMK : M * K = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_mul]
    simp only [LinearMap.comp_apply, map_zero, LinearMap.zero_apply, Matrix.toLin'_apply]
    -- x is a vector; use hKcol
    rw [hKcol]
    exact (LinearMap.mem_ker.mp (∑ j, x j • b j).2 : _)
  -- the projection onto the kernel
  have hproj : ∀ x : Fin n → ℂ, x - N *ᵥ (M *ᵥ x) ∈ LinearMap.ker (Matrix.toLin' M) := by
    intro x
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMN,
      Matrix.one_mulVec, sub_self]
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin c → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ
      (LinearMap.codRestrict (LinearMap.ker (Matrix.toLin' M))
        (LinearMap.id - Matrix.toLin' (N * M)) (fun x => by
          simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hproj x))
  let L : Matrix (Fin c) (Fin n) ℂ := LinearMap.toMatrix' f
  have hLx : ∀ x, L *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec f x
  have hLN : L * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_mul]
    simp only [LinearMap.comp_apply, map_zero, LinearMap.zero_apply, Matrix.toLin'_apply]
    rw [hLx]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (LinearMap.codRestrict (LinearMap.ker (Matrix.toLin' M))
        (LinearMap.id - Matrix.toLin' (N * M)) (fun x => by
          simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hproj x)) (N *ᵥ x) = 0 := by
      apply Subtype.ext
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, hMN]
    rw [this, map_zero]
  have hLK : L * K = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_mul]
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    rw [hLx, hKcol]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (LinearMap.codRestrict (LinearMap.ker (Matrix.toLin' M))
        (LinearMap.id - Matrix.toLin' (N * M)) (fun x => by
          simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hproj x))
          ((∑ j, x j • b j : LinearMap.ker (Matrix.toLin' M)) : Fin n → ℂ) =
          ∑ j, x j • b j := by
      apply Subtype.ext
      have hz := (∑ j, x j • b j : LinearMap.ker (Matrix.toLin' M)).2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hz
      simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
        Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]
    rw [this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  -- the complement representation
  have hNMKL : N * M + K * L = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    simp only [map_add, LinearMap.add_apply, Matrix.toLin'_apply, Matrix.toLin'_one,
      LinearMap.id_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hLx, hKcol]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    abel
  let chi : Rep G (Fin c) :=
    { toFun := fun g => L * psi2 g * K
      map_one' := by simp [hLK]
      map_mul' := by
        intro g h
        have e1 : L * psi2 (g * h) * K = L * psi2 g * (N * M + K * L) * psi2 h * K := by
          rw [hNMKL, Matrix.mul_one, map_mul]; simp only [Matrix.mul_assoc]
        rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
        have e2 : L * psi2 g * (N * M) * psi2 h * K = 0 := by
          have h0 : L * psi2 g * N = 0 := by
            rw [Matrix.mul_assoc, hNint g, ← Matrix.mul_assoc, hLN, Matrix.zero_mul]
          calc L * psi2 g * (N * M) * psi2 h * K = (L * psi2 g * N) * M * psi2 h * K := by
                simp only [Matrix.mul_assoc]
            _ = 0 := by rw [h0]; simp
        rw [e2, zero_add]
        simp only [Matrix.mul_assoc] }
  have hTS : Matrix.fromRows M L * Matrix.fromCols N K = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hMN, hMK, hLN, hLK, Matrix.fromBlocks_one]
  refine ⟨hdn, c, by omega, chi, Matrix.fromCols N K, Matrix.fromRows M L, ?_, hTS, ?_⟩
  · have e : Fin d ⊕ Fin c ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
    exact (Matrix.mul_eq_one_comm_of_equiv e).mp hTS
  · intro g
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    congr 1
    · rw [← hM g, Matrix.mul_assoc, hMN, Matrix.mul_one]
    · rw [← hM g, Matrix.mul_assoc, hMK, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, hNint g, ← Matrix.mul_assoc, hLN, Matrix.zero_mul]

end
