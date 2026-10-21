-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P25.freeSymplectic_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:21:16.767669+00:00
-- url     : https://prove2.me/submissions/c9f27391-6859-43e5-9d70-1f34017341b0

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25
noncomputable section

open MeasureTheory Filter Topology Matrix

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

open QAlgorithms.Papers.Independent.Renew46.P25



/-- PDF p.17, §3.3: free symplectic automorphisms are dense. Freeness means
invertibility of the upper-right B block, not det(S-I) nonzero. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    Dense {S : Matrix.symplecticGroup (Fin n) ℝ |
      ((S : Matrix (Phase n) (Phase n) ℝ).submatrix Sum.inl Sum.inr).det ≠ 0} := by
  classical
  intro S
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, M = (S : Matrix _ _ ℝ) := ⟨_, rfl⟩
  have hMS : M ∈ Matrix.symplecticGroup (Fin n) ℝ := hMdef ▸ S.2
  obtain ⟨A, hA⟩ : ∃ A, A = M.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = M.toBlocks₁₂ := ⟨_, rfl⟩
  have hsym : A * Bᵀ = B * Aᵀ := by
    have h := SymplecticGroup.transpose_mem hMS
    rw [← Matrix.fromBlocks_toBlocks M, Matrix.fromBlocks_transpose] at h
    have := (SymplecticGroup.fromBlocks_mem_iff.1 h).1
    simpa [hA, hB] using this
  have hdet : IsUnit M.det := SymplecticGroup.symplectic_det hMS
  let Sh : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun t => Matrix.fromBlocks 1 (t • 1) 0 1
  have hSh : ∀ t, Sh t ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    intro t
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp
  have hblock : ∀ t, (M * Sh t).submatrix Sum.inl Sum.inr = B + t • A := by
    intro t
    ext i j
    simp only [Sh, Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, hA, hB, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
    simp [Finset.sum_ite_eq', mul_comm]
    ring
  -- the exceptional parameters
  have hvdot : ∀ v w : Fin n → ℝ, (v ᵥ* B) ⬝ᵥ (w ᵥ* A) = (v ᵥ* A) ⬝ᵥ (w ᵥ* B) := by
    intro v w
    rw [← dotProduct_mulVec, ← dotProduct_mulVec, ← Matrix.mulVec_transpose A,
      ← Matrix.mulVec_transpose B, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsym]
  have hZ : {t : ℝ | (B + t • A).det = 0}.Finite := by
    by_contra hinf
    obtain ⟨s, hsZ, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    have key : ∀ t : s, ∃ v : Fin n → ℝ, v ≠ 0 ∧ v ᵥ* (B + (t : ℝ) • A) = 0 :=
      fun t => Matrix.exists_vecMul_eq_zero_iff.2 (hsZ t.2)
    choose v hv0 hv using key
    have hvB : ∀ t : s, v t ᵥ* B = -((t : ℝ) • (v t ᵥ* A)) := by
      intro t
      have := hv t
      rw [Matrix.vecMul_add, Matrix.vecMul_smul] at this
      exact eq_neg_of_add_eq_zero_left this
    let a : s → Fin n → ℝ := fun t => v t ᵥ* A
    have ha0 : ∀ t, a t ≠ 0 := by
      intro t hat
      have hB0 : v t ᵥ* B = 0 := by rw [hvB]; simp [a] at hat; simp [hat]
      let w : Fin n ⊕ Fin n → ℝ := Sum.elim (v t) 0
      have hw : w ᵥ* M = 0 := by
        funext k
        rcases k with j | j
        · have := congrFun hat j
          simp only [a, hA, Matrix.vecMul, dotProduct, Matrix.toBlocks₁₁, Matrix.of_apply] at this
          simp [w, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, this]
        · have := congrFun hB0 j
          simp only [hB, Matrix.vecMul, dotProduct, Matrix.toBlocks₁₂, Matrix.of_apply] at this
          simp [w, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, this]
      have hw0 : w = 0 := by
        have : w = (w ᵥ* M) ᵥ* M⁻¹ := by
          rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hdet, Matrix.vecMul_one]
        rw [this, hw, Matrix.zero_vecMul]
      apply hv0 t
      funext i
      have := congrFun hw0 (Sum.inl i)
      simpa [w] using this
    have horth : ∀ t u : s, t ≠ u → a t ⬝ᵥ a u = 0 := by
      intro t u htu
      have h := hvdot (v t) (v u)
      rw [hvB t, hvB u] at h
      simp only [neg_dotProduct, dotProduct_neg, smul_dotProduct,
        dotProduct_smul, smul_eq_mul] at h
      have hne : (t : ℝ) ≠ u := fun h' => htu (Subtype.ext h')
      have : ((u : ℝ) - t) * (a t ⬝ᵥ a u) = 0 := by
        simp only [a]; linarith
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
    have hli : LinearIndependent ℝ a := by
      rw [linearIndependent_iff']
      intro s' g hg i hi
      have := congrArg (fun x => x ⬝ᵥ a i) hg
      simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at this
      rw [Finset.sum_eq_single i (fun j _ hji => by rw [horth j i hji, mul_zero])
        (fun h => absurd hi h)] at this
      exact (mul_eq_zero.1 this).resolve_right (fun h => ha0 i (dotProduct_self_eq_zero.1 h))
    have := hli.fintype_card_le_finrank
    simp only [Module.finrank_fin_fun, Fintype.card_coe] at this
    omega
  -- approximate S by sheared matrices
  let f : ℝ → Matrix.symplecticGroup (Fin n) ℝ := fun t =>
    ⟨M * Sh t, Submonoid.mul_mem _ hMS (hSh t)⟩
  have hcSh : Continuous Sh :=
    Continuous.matrix_fromBlocks continuous_const (continuous_id.smul continuous_const)
      continuous_const continuous_const
  have hf : Continuous f := (continuous_const.matrix_mul hcSh).subtype_mk _
  have hf0 : f 0 = S := by
    apply Subtype.ext
    simp [f, Sh, hMdef]
  have ht : Tendsto f (𝓝[≠] 0) (𝓝 S) := by
    rw [← hf0]; exact hf.continuousAt.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have hcl : IsClosed ({t : ℝ | (B + t • A).det = 0} \ {0}) := (hZ.diff).isClosed
  have hmem : ({t : ℝ | (B + t • A).det = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    hcl.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t h1 h2
  show ((M * Sh t).submatrix Sum.inl Sum.inr).det ≠ 0
  rw [hblock]
  intro h0
  exact h1 ⟨h0, h2⟩


end
