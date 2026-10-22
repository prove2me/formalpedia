-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P13.split_family_markov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:11:40.163252+00:00
-- url     : https://prove2.me/submissions/9b37eb17-4dc1-48ad-b5f5-10354fcfb27b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction)

theorem g73w_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

theorem g73w_unit_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Mat n}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  have h1 := Unitary.star_mul_self_of_mem hU
  have h2 := Unitary.mul_star_self_of_mem hU
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact ⟨h1, h2⟩

theorem g73w_G {n : Type*} [Fintype n] [DecidableEq n] (M U : Mat n)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (μ : n → ℝ)
    (hM : M = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ) (f : ℝ → ℂ) :
    spectralFunction f M = U * Matrix.diagonal (fun i => f (μ i)) * Uᴴ := by
  obtain ⟨hUU, hUU'⟩ := g73w_unit_mul hU
  have hH : M.IsHermitian := by
    rw [hM]; exact Matrix.isHermitian_mul_mul_conjTranspose U (g73w_diag_herm μ)
  unfold spectralFunction
  rw [dif_pos hH]
  show (hH.eigenvectorUnitary : Mat n) * Matrix.diagonal (fun j => f (hH.eigenvalues j)) *
    (hH.eigenvectorUnitary : Mat n)ᴴ = _
  set V : Mat n := (hH.eigenvectorUnitary : Mat n) with hVdef
  have hVu : V ∈ Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary.2
  obtain ⟨hVV, hVV'⟩ := g73w_unit_mul hVu
  set lam : n → ℝ := hH.eigenvalues with hlam
  have hV : M = V * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * Vᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
    exact this
  set T : Mat n := Uᴴ * V with hTdef
  clear_value lam V T
  have hT : T * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (μ i : ℂ)) * T := by
    have e1 : Uᴴ * M * V = T * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
      rw [hV, hTdef]; simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
    have e2 : Uᴴ * M * V = Matrix.diagonal (fun i => (μ i : ℂ)) * T := by
      rw [hM, hTdef]; simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [← e1, e2]
  have hTf : T * Matrix.diagonal (fun j => f (lam j)) =
      Matrix.diagonal (fun i => f (μ i)) * T := by
    ext i j
    have := congrFun (congrFun hT i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this ⊢
    by_cases h0 : T i j = 0
    · simp [h0]
    · have h1 : ((lam j : ℝ) : ℂ) = (μ i : ℂ) := by
        have := this
        rw [mul_comm (μ i : ℂ)] at this
        exact mul_left_cancel₀ h0 this
      have h2 : lam j = μ i := by exact_mod_cast h1
      rw [h2, mul_comm]
  have hVT : V = U * T := by rw [hTdef, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have hTT : T * Tᴴ = 1 := by
    rw [hTdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul, hUU]
  calc V * Matrix.diagonal (fun j => f (lam j)) * Vᴴ
      = U * (T * Matrix.diagonal (fun j => f (lam j))) * Tᴴ * Uᴴ := by
        rw [hVT, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => f (μ i)) * (T * Tᴴ) * Uᴴ := by
        rw [hTf]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hTT, Matrix.mul_one]

theorem g73w_spec {n : Type*} [Fintype n] [DecidableEq n] {M : Mat n} (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Mat n) * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) *
      (hM.eigenvectorUnitary : Mat n)ᴴ := by
  have := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
  exact this

theorem g73w_sf_def {n : Type*} [Fintype n] [DecidableEq n] {M : Mat n} (hM : M.IsHermitian)
    (f : ℝ → ℂ) : spectralFunction f M = (hM.eigenvectorUnitary : Mat n) *
      Matrix.diagonal (fun i => f (hM.eigenvalues i)) * (hM.eigenvectorUnitary : Mat n)ᴴ :=
  g73w_G M _ hM.eigenvectorUnitary.2 _ (g73w_spec hM) f

theorem g73w_unit_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (V1 : Matrix.unitaryGroup α ℂ) (V2 : Matrix.unitaryGroup β ℂ) :
    Matrix.fromBlocks (V1 : Mat α) 0 0 (V2 : Mat β) ∈ Matrix.unitaryGroup (α ⊕ β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1 := Unitary.star_mul_self_of_mem V1.2
  have h2 := Unitary.star_mul_self_of_mem V2.2
  rw [Matrix.star_eq_conjTranspose] at h1 h2 ⊢
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h1, h2,
    Matrix.fromBlocks_one]

theorem g73w_sf_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X : Mat α} {Y : Mat β} (hX : X.IsHermitian) (hY : Y.IsHermitian) (f : ℝ → ℂ) :
    spectralFunction f (Matrix.fromBlocks X 0 0 Y) =
      Matrix.fromBlocks (spectralFunction f X) 0 0 (spectralFunction f Y) := by
  have hW := g73w_unit_blocks hX.eigenvectorUnitary hY.eigenvectorUnitary
  have hdec : Matrix.fromBlocks X 0 0 Y =
      Matrix.fromBlocks (hX.eigenvectorUnitary : Mat α) 0 0 (hY.eigenvectorUnitary : Mat β) *
      Matrix.diagonal (fun i => ((Sum.elim hX.eigenvalues hY.eigenvalues i : ℝ) : ℂ)) *
      (Matrix.fromBlocks (hX.eigenvectorUnitary : Mat α) 0 0 (hY.eigenvectorUnitary : Mat β))ᴴ := by
    have e : (fun i => ((Sum.elim hX.eigenvalues hY.eigenvalues i : ℝ) : ℂ)) =
        Sum.elim (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) := by
      funext i; cases i <;> rfl
    rw [e, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    conv_lhs => rw [g73w_spec hX, g73w_spec hY]
    simp
  rw [g73w_G _ _ hW _ hdec f, g73w_sf_def hX, g73w_sf_def hY]
  have e : (fun i => f (Sum.elim hX.eigenvalues hY.eigenvalues i)) =
      Sum.elim (fun i => f (hX.eigenvalues i)) (fun i => f (hY.eigenvalues i)) := by
    funext i; cases i <;> rfl
  rw [e, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem g73w_sf_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {M : Mat β} (hM : M.IsHermitian) (f : ℝ → ℂ) :
    spectralFunction f (M.submatrix e e) = (spectralFunction f M).submatrix e e := by
  set V : Mat β := (hM.eigenvectorUnitary : Mat β)
  obtain ⟨hVV, hVV'⟩ := g73w_unit_mul hM.eigenvectorUnitary.2
  have hU : V.submatrix e e ∈ Matrix.unitaryGroup α ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, hVV, Matrix.submatrix_one_equiv]
  have hdec : M.submatrix e e = V.submatrix e e *
      Matrix.diagonal (fun i => ((hM.eigenvalues (e i) : ℝ) : ℂ)) * (V.submatrix e e)ᴴ := by
    have h1 : Matrix.diagonal (fun i => ((hM.eigenvalues (e i) : ℝ) : ℂ)) =
        (Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ))).submatrix e e := by
      rw [Matrix.submatrix_diagonal_equiv]; rfl
    rw [h1, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    conv_lhs => rw [g73w_spec hM]
  rw [g73w_G _ _ hU _ hdec f, g73w_sf_def hM]
  have h1 : Matrix.diagonal (fun i => f (hM.eigenvalues (e i))) =
      (Matrix.diagonal (fun i => f (hM.eigenvalues i))).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]; rfl
  rw [h1, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem g73w_four {n : Type*} [Fintype n] [DecidableEq n] (M U : Mat n)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (μ : n → ℝ)
    (hM : M = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ) (hμ : ∀ i, 0 < μ i) (t : ℝ) :
    imaginaryPower M t * imaginaryPower (1 + M) (-t) * imaginaryPower M (-t) *
      imaginaryPower (1 + M) t = 1 := by
  obtain ⟨hUU, hUU'⟩ := g73w_unit_mul hU
  have h1 : 1 + M = U * Matrix.diagonal (fun i => ((1 + μ i : ℝ) : ℂ)) * Uᴴ := by
    have : Matrix.diagonal (fun i => ((1 + μ i : ℝ) : ℂ)) =
        1 + Matrix.diagonal (fun i => (μ i : ℂ)) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]; congr 1; funext i; push_cast; ring
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU', hM]
  unfold imaginaryPower
  rw [g73w_G _ _ hU _ hM, g73w_G _ _ hU _ h1, g73w_G _ _ hU _ hM, g73w_G _ _ hU _ h1]
  have key : ∀ (D1 D2 D3 D4 : n → ℂ), U * Matrix.diagonal D1 * Uᴴ * (U * Matrix.diagonal D2 * Uᴴ) *
      (U * Matrix.diagonal D3 * Uᴴ) * (U * Matrix.diagonal D4 * Uᴴ) =
      U * Matrix.diagonal (fun i => D1 i * D2 i * D3 i * D4 i) * Uᴴ := by
    intro D1 D2 D3 D4
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    congr 3; funext i; ring
  rw [key]
  have hd : (fun i => QAlgorithms.Papers.Independent.Dependency50.P21.imaginaryScalar t (μ i) *
      QAlgorithms.Papers.Independent.Dependency50.P21.imaginaryScalar (-t) (1 + μ i) *
      QAlgorithms.Papers.Independent.Dependency50.P21.imaginaryScalar (-t) (μ i) *
      QAlgorithms.Papers.Independent.Dependency50.P21.imaginaryScalar t (1 + μ i)) = fun _ => 1 := by
    funext i
    have a := (hμ i).ne'
    have b : 1 + μ i ≠ 0 := by linarith [hμ i]
    simp only [QAlgorithms.Papers.Independent.Dependency50.P21.imaginaryScalar, a, b, if_false]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  rw [hd, Matrix.diagonal_one, Matrix.mul_one, hUU']

theorem g73w_cfc_sf {n : Type*} [Fintype n] [DecidableEq n] {M : Mat n} (hM : M.IsHermitian)
    (f : ℝ → ℝ) : cfc f M = spectralFunction (fun x => (f x : ℂ)) M := by
  rw [g73w_sf_def hM, hM.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose]
  rfl

theorem g73w_ent_sf {n : Type*} [Fintype n] [DecidableEq n] {M : Mat n} (hM : M.IsHermitian) :
    covarianceEntropy M = (spectralFunction (fun x => (entropyMode x : ℂ)) M).trace.re := by
  unfold covarianceEntropy; rw [g73w_cfc_sf hM]

theorem g73w_ent_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X : Mat α} {Y : Mat β} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    covarianceEntropy (Matrix.fromBlocks X 0 0 Y) = covarianceEntropy X + covarianceEntropy Y := by
  rw [g73w_ent_sf (hX.fromBlocks (by simp) hY), g73w_ent_sf hX, g73w_ent_sf hY, g73w_sf_blocks hX hY]
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem g73w_ent_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {M : Mat β} (hM : M.IsHermitian) :
    covarianceEntropy (M.submatrix e e) = covarianceEntropy M := by
  rw [g73w_ent_sf (hM.submatrix e), g73w_ent_sf hM, g73w_sf_reindex e hM]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun j => spectralFunction (fun x => (entropyMode x : ℂ)) M j j)

theorem g73w_quad_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (X : Mat α) (Y : Mat β) (x : α ⊕ β → ℂ) :
    star x ⬝ᵥ (Matrix.fromBlocks X 0 0 Y *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (X *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (Y *ᵥ (x ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply,
    Function.comp_apply]

theorem g73w_psd_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X : Mat α} {Y : Mat β} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (Matrix.fromBlocks X 0 0 Y).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hX hY ⊢
  refine ⟨hX.1.fromBlocks (by simp) hY.1, fun x => ?_⟩
  rw [g73w_quad_blocks]
  exact add_nonneg (hX.2 _) (hY.2 _)

theorem g73w_pd_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X : Mat α} {Y : Mat β} (hX : X.PosDef) (hY : Y.PosDef) :
    (Matrix.fromBlocks X 0 0 Y).PosDef := by
  have hX' := Matrix.posSemidef_iff_dotProduct_mulVec.mp hX.posSemidef
  have hY' := Matrix.posSemidef_iff_dotProduct_mulVec.mp hY.posSemidef
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hX hY ⊢
  refine ⟨hX.1.fromBlocks (by simp) hY.1, fun x hx => ?_⟩
  rw [g73w_quad_blocks]
  by_cases h1 : x ∘ Sum.inl = 0
  · have h2 : x ∘ Sum.inr ≠ 0 := by
      intro h2; apply hx; funext i; cases i with
      | inl a => exact congrFun h1 a
      | inr b => exact congrFun h2 b
    exact add_pos_of_nonneg_of_pos (hX'.2 _) (hY.2 h2)
  · exact add_pos_of_pos_of_nonneg (hX.2 h1) (hY'.2 _)

def g73w_g (I Ja Jb K : Type*) : I ⊕ ((Ja ⊕ Jb) ⊕ K) ≃ (I ⊕ Ja) ⊕ (Jb ⊕ K) where
  toFun := refinedIndex
  invFun := fun x => match x with
    | .inl (.inl i) => .inl i
    | .inl (.inr j) => .inr (.inl (.inl j))
    | .inr (.inl j) => .inr (.inl (.inr j))
    | .inr (.inr k) => .inr (.inr k)
  left_inv := by intro x; rcases x with i | ((j | j) | k) <;> rfl
  right_inv := by intro x; rcases x with (i | j) | (j | k) <;> rfl

theorem g73w_one_add_sub {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (M : Mat β) : 1 + M.submatrix e e = (1 + M).submatrix e e := by
  rw [← Matrix.submatrix_one_equiv e, Matrix.submatrix_add]
  rfl

theorem g73w_one_add_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (X : Mat α) (Y : Mat β) : 1 + Matrix.fromBlocks X 0 0 Y = Matrix.fromBlocks (1 + X) 0 0 (1 + Y) := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp

theorem g73w_dec_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {X U : Mat α} {Y U' : Mat β} (μ : α → ℝ) (μ' : β → ℝ)
    (hX : X = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ)
    (hY : Y = U' * Matrix.diagonal (fun i => (μ' i : ℂ)) * U'ᴴ) :
    Matrix.fromBlocks X 0 0 Y = Matrix.fromBlocks U 0 0 U' *
      Matrix.diagonal (fun i => ((Sum.elim μ μ' i : ℝ) : ℂ)) * (Matrix.fromBlocks U 0 0 U')ᴴ := by
  have e : (fun i => ((Sum.elim μ μ' i : ℝ) : ℂ)) =
      Sum.elim (fun i => ((μ i : ℝ) : ℂ)) (fun i => ((μ' i : ℝ) : ℂ)) := by
    funext i; cases i <;> rfl
  rw [e, ← Matrix.fromBlocks_diagonal, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, hX, hY]
  simp

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem g73w_cp_pd : correlatedPair.PosDef := by
  have h1 : (((3:ℂ)/2) • (1 : Mat (Fin 1 ⊕ Fin 1))).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  let B : Matrix Unit (Fin 1 ⊕ Fin 1) ℂ := Matrix.of fun _ _ => 1
  have h2 : (((1:ℂ)/2) • (Bᴴ * B)).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self B).smul (by norm_num [Complex.le_def])
  have h3 : correlatedPair = ((3:ℂ)/2) • (1 : Mat (Fin 1 ⊕ Fin 1)) + ((1:ℂ)/2) • (Bᴴ * B) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [correlatedPair, B, Matrix.mul_apply, Matrix.one_apply, Fin.fin_one_eq_zero] <;> norm_num
  rw [h3]
  exact h1.add_posSemidef h2

theorem g73w_markov {Ja Jb : Type*} [Fintype Ja] [Fintype Jb]
    [DecidableEq Ja] [DecidableEq Jb] (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K))
    (hL : L.IsHermitian) (hR : R.IsHermitian) : IsMarkov (splitCovariance L R) := by
  have hA : splitCovariance L R = (Matrix.fromBlocks L 0 0 R).submatrix (g73w_g I Ja Jb K)
      (g73w_g I Ja Jb K) := rfl
  have h23 : marginal23 (splitCovariance L R) =
      (Matrix.fromBlocks (L.submatrix Sum.inr Sum.inr) 0 0 R).submatrix (Equiv.sumAssoc Ja Jb K)
        (Equiv.sumAssoc Ja Jb K) := by
    ext a b; rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> rfl
  have h12 : marginal12 (splitCovariance L R) =
      (Matrix.fromBlocks L 0 0 (R.submatrix Sum.inl Sum.inl)).submatrix
        (Equiv.sumAssoc I Ja Jb).symm (Equiv.sumAssoc I Ja Jb).symm := by
    ext a b; rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> rfl
  have h22 : a22 (splitCovariance L R) =
      Matrix.fromBlocks (L.submatrix Sum.inr Sum.inr) 0 0 (R.submatrix Sum.inl Sum.inl) := by
    ext a b; rcases a with a | a <;> rcases b with b | b <;> rfl
  have hLa := hL.submatrix (Sum.inr : Ja → I ⊕ Ja)
  have hRb := hR.submatrix (Sum.inl : Jb → Jb ⊕ K)
  unfold IsMarkov
  rw [h23, h12, h22, hA, g73w_ent_reindex _ (hL.fromBlocks (by simp) hR),
    g73w_ent_reindex _ (hLa.fromBlocks (by simp) hR), g73w_ent_reindex _ (hL.fromBlocks (by simp) hRb),
    g73w_ent_blocks hL hR, g73w_ent_blocks hLa hR, g73w_ent_blocks hL hRb, g73w_ent_blocks hLa hRb]
  ring

theorem g73w_power {Ja Jb : Type*} [Fintype Ja] [Fintype Jb]
    [DecidableEq Ja] [DecidableEq Jb] (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K))
    (hL : L.PosDef) (hR : R.PosDef) : PowerCondition (splitCovariance L R) := by
  intro t
  set g := g73w_g I Ja Jb K
  set Laa := L.submatrix (Sum.inr : Ja → I ⊕ Ja) Sum.inr
  set Rbb := R.submatrix (Sum.inl : Jb → Jb ⊕ K) Sum.inl
  set Q : Mat (I ⊕ Ja) := Matrix.fromBlocks 1 0 0 Laa
  set P : Mat (Jb ⊕ K) := Matrix.fromBlocks Rbb 0 0 1
  have hLh := hL.1
  have hRh := hR.1
  have hLa : Laa.IsHermitian := hLh.submatrix _
  have hRbd : Rbb.PosDef := hR.submatrix Sum.inl_injective
  have hRb : Rbb.IsHermitian := hRbd.1
  have hQ : Q.IsHermitian := Matrix.isHermitian_one.fromBlocks (by simp) hLa
  have hP : P.IsHermitian := hRb.fromBlocks (by simp) Matrix.isHermitian_one
  have hA : splitCovariance L R = (Matrix.fromBlocks L 0 0 R).submatrix g g := rfl
  have hD : dMatrix (splitCovariance L R) = (Matrix.fromBlocks Q 0 0 R).submatrix g g := by
    ext a b
    rcases a with a | ((a | a) | a) <;> rcases b with b | ((b | b) | b) <;> rfl
  have hB : bMatrix (splitCovariance L R) = (Matrix.fromBlocks L 0 0 P).submatrix g g := by
    ext a b
    rcases a with a | ((a | a) | a) <;> rcases b with b | ((b | b) | b) <;> rfl
  have hC : cMatrix (splitCovariance L R) = (Matrix.fromBlocks Q 0 0 P).submatrix g g := by
    ext a b
    rcases a with a | ((a | a) | a) <;> rcases b with b | ((b | b) | b) <;> rfl
  have hip : ∀ {X : Mat (I ⊕ Ja)} {Y : Mat (Jb ⊕ K)}, X.IsHermitian → Y.IsHermitian →
      ∀ s : ℝ, imaginaryPower ((Matrix.fromBlocks X 0 0 Y).submatrix g g) s =
        (Matrix.fromBlocks (imaginaryPower X s) 0 0 (imaginaryPower Y s)).submatrix g g := by
    intro X Y hX hY s
    unfold imaginaryPower
    rw [g73w_sf_reindex g (hX.fromBlocks (by simp) hY), g73w_sf_blocks hX hY]
  have hip1 : ∀ {X : Mat (I ⊕ Ja)} {Y : Mat (Jb ⊕ K)}, X.IsHermitian → Y.IsHermitian →
      ∀ s : ℝ, imaginaryPower (1 + (Matrix.fromBlocks X 0 0 Y).submatrix g g) s =
        (Matrix.fromBlocks (imaginaryPower (1 + X) s) 0 0
          (imaginaryPower (1 + Y) s)).submatrix g g := by
    intro X Y hX hY s
    rw [g73w_one_add_sub, g73w_one_add_blocks, hip (Matrix.isHermitian_one.add hX) (Matrix.isHermitian_one.add hY)]
  rw [hD, hB, hC, hA, hip hLh hRh, hip1 hLh hRh, hip hQ hRh, hip1 hQ hRh, hip hLh hP, hip1 hLh hP,
    hip hQ hP, hip1 hQ hP]
  simp only [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  -- R-parts
  have hR4 := g73w_four R _ hRh.eigenvectorUnitary.2 _ (g73w_spec hRh) (hR.eigenvalues_pos) t
  have hPdec := g73w_dec_blocks (X := Rbb) (Y := (1 : Mat K)) (U' := (1 : Mat K)) hRb.eigenvalues (fun _ => (1 : ℝ))
    (g73w_spec hRb) (by simp)
  have hP4 := g73w_four P _ (g73w_unit_blocks hRb.eigenvectorUnitary 1) _ hPdec
    (fun i => by cases i with
      | inl a => exact hRbd.eigenvalues_pos a
      | inr k => exact one_pos) t
  simp only [Matrix.mul_assoc] at hR4 hP4 ⊢
  rw [hR4, hP4]

theorem solution {Ja Jb : Type*} [Fintype Ja] [Fintype Jb]
    [DecidableEq Ja] [DecidableEq Jb] (L : Mat (I ⊕ Ja)) (R : Mat (Jb ⊕ K))
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    (splitCovariance L R).PosSemidef ∧ IsMarkov (splitCovariance L R) ∧
    (L.PosDef → R.PosDef → PowerCondition (splitCovariance L R)) ∧
    (let A := splitCovariance correlatedPair correlatedPair
     A.PosDef ∧ IsMarkov A ∧ a12 A ≠ 0 ∧ a23 A ≠ 0) := by
  refine ⟨?_, g73w_markov L R hL.1 hR.1, fun hLd hRd => g73w_power L R hLd hRd, ?_⟩
  · exact Matrix.posSemidef_submatrix_equiv (g73w_g I Ja Jb K) |>.mpr (g73w_psd_blocks hL hR)
  · intro A
    have hcp := g73w_cp_pd
    refine ⟨?_, g73w_markov _ _ hcp.1 hcp.1, ?_, ?_⟩
    · exact (g73w_pd_blocks hcp hcp).submatrix (g73w_g _ _ _ _).injective
    · intro h
      have := congrFun (congrFun h 0) (Sum.inl 0)
      have e : a12 A 0 (Sum.inl 0) = 1 / 2 := rfl
      rw [e] at this
      norm_num at this
    · intro h
      have := congrFun (congrFun h (Sum.inr 0)) 0
      have e : a23 A (Sum.inr 0) 0 = 1 / 2 := rfl
      rw [e] at this
      norm_num at this
