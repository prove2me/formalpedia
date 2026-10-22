-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.proper_diagonal_subclass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:39:38.04749+00:00
-- url     : https://prove2.me/submissions/5c465ee3-d411-436f-969d-098040ebb45f

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68q_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68q_kc2 (E : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (a b : K) :
    complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace := by
  simp only [complementaryChannel, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68q_kc3 (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext rho; ext a b
  rw [g68q_kc2]
  simp only [krausApply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]

theorem g68q_row_tr (F : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (l l' : K) :
    krausApply (rowKraus F) rho l l' = (F l * rho * (F l')ᴴ).trace := by
  have := g68q_kc2 F rho l l'
  rw [← this, g68q_kc3]

theorem g68q_col_zero {n : ℕ} (B' : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (h : (B'ᴴ * B') i i = 0) (l : Fin n) :
    B' l i = 0 := by
  have h2 : (B'ᴴ * B') i i = ((∑ l, ‖B' l i‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.mul_apply, Complex.conj_mul']
  rw [h2, Complex.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h
  simpa using h l (Finset.mem_univ _)

theorem g68q_part1 : ∀ (n m : ℕ), 0 < n → ∀ Phi : Superop (Fin n) (Fin m),
      DiagonalEquivalent Phi → EBComplement Phi := by
  intro n m _ Phi ⟨D, ⟨c, hc, U, hD⟩, W, hW, hPhi, hD2⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin n) (Fin n) ℂ, c = B'ᴴ * B' := by
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hc.nonneg
    exact ⟨B, hB⟩
  set Um : Matrix (Fin n) (Fin n) ℂ := (U : Matrix (Fin n) (Fin n) ℂ) with hUm
  have hU1 : Umᴴ * Um = 1 := by
    rw [hUm, ← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp U.2
  have hU2 : Um * Umᴴ = 1 := by
    rw [hUm, ← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp U.2
  set X := W * Um with hX
  set M := Xᴴ * X with hM
  set x : Fin n → Fin n → ℂ := fun l i => star (B' l i) with hx
  set F : Fin n → Matrix (Fin m) (Fin n) ℂ := fun l => X * Matrix.diagonal (x l) * Umᴴ with hF
  set psi : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun a => Um a i) with hpsi
  set phi : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun l => x l i) with hphi
  -- Phi as Kraus
  have hhad : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      c ⊙ Y = ∑ l, Matrix.diagonal (x l) * Y * (Matrix.diagonal (x l))ᴴ := by
    intro Y; ext i j
    rw [Matrix.hadamard_apply, Matrix.sum_apply]
    simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hB', Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [hx, Pi.star_apply, star_star, Matrix.conjTranspose_apply]
    ring
  have hPhiK : Phi = krausApply F := by
    funext rho
    rw [hPhi, hD, hhad]
    simp only [krausApply]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [hF, hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hP2 : M * M = M := by
    have h1 : M * M = Umᴴ * Wᴴ * (W * Wᴴ * W) * Um := by
      simp only [hM, hX, Matrix.conjTranspose_mul]
      rw [show Umᴴ * Wᴴ * (W * Um) * (Umᴴ * Wᴴ * (W * Um)) = Umᴴ * Wᴴ * W * (Um * Umᴴ) * Wᴴ * W * Um by
        simp only [Matrix.mul_assoc], hU2]
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [h1, hW]; simp only [hM, hX, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hDP : ∀ rho, D rho = Wᴴ * W * D rho * Wᴴ * W := by
    intro rho; conv_lhs => rw [hD2, hPhi]
    simp only [Matrix.mul_assoc]
  have hcol : ∀ i, c i i ≠ 0 → ∀ a, M a i = if a = i then 1 else 0 := by
    intro i hci
    have hE := hDP (Um * Matrix.single i i 1 * Umᴴ)
    have hY : Umᴴ * (Um * Matrix.single i i 1 * Umᴴ) * Um = Matrix.single i i 1 := by
      rw [show Umᴴ * (Um * Matrix.single i i 1 * Umᴴ) * Um = (Umᴴ * Um) * Matrix.single i i 1 * (Umᴴ * Um) by
        simp only [Matrix.mul_assoc], hU1, Matrix.one_mul, Matrix.mul_one]
    have hS : c ⊙ Matrix.single i i (1 : ℂ) = c i i • Matrix.single i i 1 := by
      ext a b
      simp only [Matrix.hadamard_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases h : i = a ∧ i = b
      · obtain ⟨rfl, rfl⟩ := h; simp
      · simp [h]
    rw [hD, hY, hS] at hE
    have hE2 := congrArg (fun Z => Umᴴ * Z * Um) hE
    rw [show Umᴴ * (Um * (c i i • Matrix.single i i 1) * Umᴴ) * Um = (Umᴴ * Um) * (c i i • Matrix.single i i 1) * (Umᴴ * Um) by
        simp only [Matrix.mul_assoc], hU1, Matrix.one_mul, Matrix.mul_one] at hE2
    rw [show Umᴴ * (Wᴴ * W * (Um * (c i i • Matrix.single i i 1) * Umᴴ) * Wᴴ * W) * Um =
        M * (c i i • Matrix.single i i 1) * M by
        simp only [hM, hX, Matrix.conjTranspose_mul, Matrix.mul_assoc]] at hE2
    have h3 : ∀ a b, M a i * M i b = if a = i ∧ b = i then 1 else 0 := by
      intro a b
      have := congrFun (congrFun hE2 a) b
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.smul_apply] at this
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
      simp only [true_and, if_true] at this
      apply mul_right_cancel₀ hci
      by_cases h : a = i ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [and_self, if_true] at this ⊢
        linear_combination -this
      · have h' : ¬ (i = a ∧ i = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
        simp only [h, h', if_false] at this ⊢
        linear_combination -this
    have hii2 : M i i * M i i = 1 := by simpa using h3 i i
    have hii0 : M i i ≠ 0 := by intro h0; rw [h0] at hii2; simp at hii2
    have hrow : ∀ b, b ≠ i → M i b = 0 := by
      intro b hb
      have := h3 i b
      simp only [hb, and_false, if_false] at this
      exact (mul_eq_zero.mp this).resolve_left hii0
    have hcol0 : ∀ a, a ≠ i → M a i = 0 := by
      intro a ha
      have := h3 a i
      simp only [ha, false_and, if_false] at this
      exact (mul_eq_zero.mp this).resolve_right hii0
    have hii : M i i = 1 := by
      have := congrFun (congrFun hP2 i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun b _ hb => by rw [hrow b hb, zero_mul]) (by simp)] at this
      rw [this] at hii2; exact hii2
    intro a
    by_cases ha : a = i
    · subst ha; simp [hii]
    · simp [ha, hcol0 a ha]
  have hx0 : ∀ i, c i i = 0 → ∀ l, x l i = 0 := by
    intro i hi l
    simp only [hx, star_eq_zero]
    exact g68q_col_zero B' i (hB' ▸ hi) l
  have key : ∀ l l' i i', star (x l' i) * M i i' * x l i' =
      if i = i' then star (x l' i) * x l i else 0 := by
    intro l l' i i'
    by_cases hi : c i i = 0
    · simp [hx0 i hi l']
    by_cases hi' : c i' i' = 0
    · simp only [hx0 i' hi' l, mul_zero]
      split_ifs with h
      · subst h; simp [hx0 _ hi' l]
      · rfl
    rw [hcol i' hi' i]
    by_cases h : i = i'
    · subst h; simp
    · simp [h]
  have hdiag : ∀ l l', (Matrix.diagonal (x l'))ᴴ * M * Matrix.diagonal (x l) =
      Matrix.diagonal (fun i => star (x l' i) * x l i) := by
    intro l l'
    ext i i'
    simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
    rw [key, Matrix.diagonal_apply]
  have hEK : krausApply (rowKraus F) = krausApply (rankOneKraus psi phi) := by
    funext rho
    ext l l'
    rw [g68q_row_tr]
    have e1 : (F l * rho * (F l')ᴴ).trace =
        ((Matrix.diagonal (x l'))ᴴ * M * Matrix.diagonal (x l) * (Umᴴ * rho * Um)).trace := by
      set Dl := Matrix.diagonal (x l) with hDl
      set Dl' := Matrix.diagonal (x l') with hDl'
      set Y := Umᴴ * rho * Um with hY
      calc (F l * rho * (F l')ᴴ).trace
          = (X * ((Dl * Y * Dl'ᴴ) * Xᴴ)).trace := by
            congr 1
            simp only [hF, hY, hDl, hDl', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = (((Dl * Y * Dl'ᴴ) * Xᴴ) * X).trace := Matrix.trace_mul_comm _ _
        _ = (Dl * (Y * Dl'ᴴ * M)).trace := by congr 1; simp only [hM, Matrix.mul_assoc]
        _ = ((Y * Dl'ᴴ * M) * Dl).trace := Matrix.trace_mul_comm _ _
        _ = (Y * (Dl'ᴴ * M * Dl)).trace := by congr 1; simp only [Matrix.mul_assoc]
        _ = _ := Matrix.trace_mul_comm _ _
    rw [e1, hdiag, Matrix.trace]
    simp only [Matrix.diag, Matrix.diagonal_mul]
    simp only [krausApply, rankOneKraus, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, hpsi, hphi]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [star_mul', RCLike.star_def, Complex.conj_conj]
    ring
  refine ⟨n, krausApply (rankOneKraus psi phi), ⟨n, psi, phi, rfl⟩, indexedKrausDilation (rowKraus F), ?_, ?_⟩
  · rw [g68q_kc1, hEK]
  · rw [g68q_kc3, hPhiK]; rfl

theorem g68q_part2 :
    (∃ Phi : Superop (Fin 1) (Fin 2),
      Phi = (fun rho => (rho.trace / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      IsChannel Phi ∧ EBComplement Phi ∧ ¬ DiagonalEquivalent Phi) := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · let g : Fin 4 → Fin 2 := ![0, 0, 1, 1]
    refine ⟨4, fun b => (1/2 : ℂ) • Matrix.single (g b) 0 1, ?_, ?_⟩
    · simp only [IsKrausFamily]
      ext i j
      fin_cases i; fin_cases j
      simp [Fin.sum_univ_four, g, Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
      norm_num
    · intro rho
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [krausApply, Fin.sum_univ_four, g, Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply,
          Matrix.trace, Fin.sum_univ_one] <;> ring
  · let psi : Fin 2 → EuclideanSpace ℂ (Fin 1) := fun _ => WithLp.toLp 2 (fun _ => 1)
    let phi : Fin 2 → EuclideanSpace ℂ (Fin 4) := fun c => WithLp.toLp 2 (fun b => if (b : ℕ) / 2 = c then 1/2 else 0)
    refine ⟨4, krausApply (rankOneKraus psi phi), ⟨2, psi, phi, rfl⟩,
      indexedKrausDilation (rankOneKraus psi phi), g68q_kc1 _, ?_⟩
    rw [g68q_kc3]
    funext rho
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [krausApply, rowKraus, rankOneKraus, Fin.sum_univ_four, psi, phi, Matrix.mul_apply, Matrix.sum_apply,
        Matrix.trace, Fin.sum_univ_one, Fin.sum_univ_two, map_ofNat] <;> ring
  · rintro ⟨D, _, W, _, hPhi, _⟩
    have h := hPhi 1
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Matrix.trace, Fin.sum_univ_one] at h00 h11 h01
    rcases h01 with (h | h) | h <;> simp [h] at h00 h11

theorem solution :
    (∀ (n m : ℕ), 0 < n → ∀ Phi : Superop (Fin n) (Fin m),
      DiagonalEquivalent Phi → EBComplement Phi) ∧
    (∃ Phi : Superop (Fin 1) (Fin 2),
      Phi = (fun rho => (rho.trace / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      IsChannel Phi ∧ EBComplement Phi ∧ ¬ DiagonalEquivalent Phi) :=
  ⟨g68q_part1, g68q_part2⟩
