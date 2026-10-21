-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P22.smith_saturation_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:12:59.624091+00:00
-- url     : https://prove2.me/submissions/50f81fef-45f7-4d01-85d7-3fcb82f9e675

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Relations

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

theorem g64n_memZ (alpha : Fin n → K) (v : Fin n → ℤ) :
    v ∈ relationKernel ℤ alpha ↔ ∑ j, (v j : K) * alpha j = 0 := by
  simp [relationKernel]

theorem g64n_memQ (alpha : Fin n → K) (v : Fin n → ℚ) :
    v ∈ relationKernel ℚ alpha ↔ ∑ j, (v j : K) * alpha j = 0 := by
  simp [relationKernel]

theorem g64n_vecMul_eq {R : Type*} [CommRing R] (c : Fin m → R) (B : Matrix (Fin m) (Fin n) R) :
    Matrix.vecMul c B = ∑ i, c i • B i := by
  funext j; simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem g64n_rowsZ (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha B) (i : Fin m) : B i ∈ relationKernel ℤ alpha := by
  have h : (fun j => (B i j : ℚ)) ∈ relationKernel ℚ alpha := by
    rw [← hB.2]; exact Submodule.subset_span ⟨i, rfl⟩
  rw [g64n_memQ] at h; rw [g64n_memZ]; simpa using h

theorem g64n_linZ (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha B) : LinearIndependent ℤ B := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg i
  have h := (Fintype.linearIndependent_iff.mp hB.1) (fun i => (g i : ℚ)) (by
    funext j
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    exact_mod_cast this) i
  exact_mod_cast h

theorem g64n_spanZ (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha B) (c : Fin m → ℤ) :
    ∑ k, c k • B k ∈ relationKernel ℤ alpha :=
  Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (g64n_rowsZ alpha B hB k))

theorem g64n_fwd (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha B) (D : SmithData B) (hI : IntegerRowsBasis alpha B) (i : Fin m) :
    D.factors i = 1 := by
  set P : Matrix (Fin m) (Fin m) ℤ := (D.P : Matrix (Fin m) (Fin m) ℤ)
  set Pinv : Matrix (Fin m) (Fin m) ℤ := ((D.P⁻¹ : (Matrix (Fin m) (Fin m) ℤ)ˣ) : Matrix (Fin m) (Fin m) ℤ)
  set Q : Matrix (Fin n) (Fin n) ℤ := (D.Q : Matrix (Fin n) (Fin n) ℤ)
  set Qinv : Matrix (Fin n) (Fin n) ℤ := ((D.Q⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ)
  have hPP : P * Pinv = 1 := D.P.mul_inv
  have hQQ : Q * Qinv = 1 := D.Q.mul_inv
  have heq : P * B * Q = rectangularDiagonal m n D.factors := D.equation
  let i' : Fin n := ⟨i.val, lt_of_lt_of_le i.2 D.rows_le_cols⟩
  set d := D.factors i
  have hd : 0 < d := D.positive i
  set x : Fin m → ℤ := P i
  set y : Fin n → ℤ := Qinv i'
  have hPB : P * B = rectangularDiagonal m n D.factors * Qinv := by
    rw [← heq, Matrix.mul_assoc (P * B), hQQ, Matrix.mul_one]
  have hxy : ∑ k, x k • B k = d • y := by
    funext j
    have h1 := congrFun (congrFun hPB i) j
    simp only [Matrix.mul_apply, rectangularDiagonal] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x, y]
    rw [show (∑ k, P i k * B k j) = ∑ k, P i k * B k j from rfl, h1]
    rw [Finset.sum_eq_single i']
    · simp [i', d]
    · intro b _ hb
      have : ¬ (i.val = b.val) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  have hyL : y ∈ relationKernel ℤ alpha := by
    have h := g64n_spanZ alpha B hB x
    rw [hxy, g64n_memZ] at h
    rw [g64n_memZ]
    have hdK : (d : K) ≠ 0 := by exact_mod_cast hd.ne'
    have : (d : K) * ∑ j, (y j : K) * alpha j = 0 := by
      rw [Finset.mul_sum, ← h]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hdK
  rw [← hI.2] at hyL
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hyL
  have hlin : ∀ k, d * c k = x k := by
    have := Fintype.linearIndependent_iff.mp hI.1 (fun k => d * c k - x k) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hxy, mul_smul]
      rw [← Finset.smul_sum, hc, sub_self])
    intro k; have := this k; linarith
  have h1 := congrFun (congrFun hPP i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : d ∣ 1 := by
    refine ⟨∑ k, c k * Pinv k i, ?_⟩
    rw [← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have := hlin k; simp only [x] at this; rw [← this]; ring
  exact Int.eq_one_of_dvd_one hd.le this

theorem g64n_bwd (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha B) (D : SmithData B) (h1 : ∀ i, D.factors i = 1) :
    IntegerRowsBasis alpha B := by
  refine ⟨g64n_linZ alpha B hB, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact g64n_rowsZ alpha B hB k
  intro v hv
  have hvq : (fun j => (v j : ℚ)) ∈ relationKernel ℚ alpha := by
    rw [g64n_memZ] at hv; rw [g64n_memQ]; simpa using hv
  rw [← hB.2] at hvq
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hvq
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  set P : Matrix (Fin m) (Fin m) ℤ := (D.P : Matrix (Fin m) (Fin m) ℤ)
  set Pinv : Matrix (Fin m) (Fin m) ℤ := ((D.P⁻¹ : (Matrix (Fin m) (Fin m) ℤ)ˣ) : Matrix (Fin m) (Fin m) ℤ)
  set Q : Matrix (Fin n) (Fin n) ℤ := (D.Q : Matrix (Fin n) (Fin n) ℤ)
  have hPP : Pinv * P = 1 := D.P.inv_mul
  have heq : P * B * Q = rectangularDiagonal m n D.factors := D.equation
  have hBQ : B * Q = Pinv * rectangularDiagonal m n D.factors := by
    rw [← heq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hBQq : B.map φ * Q.map φ = Pinv.map φ * (rectangularDiagonal m n D.factors).map φ := by
    rw [← Matrix.map_mul, hBQ, Matrix.map_mul]
  have hPPq : Pinv.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one] <;> simp
  have hvq' : (fun j => (v j : ℚ)) = Matrix.vecMul q (B.map φ) := by
    rw [g64n_vecMul_eq, ← hq]; rfl
  set w := Matrix.vecMul q (Pinv.map φ) with hw
  have hw1 : Matrix.vecMul (fun j => (v j : ℚ)) (Q.map φ) = Matrix.vecMul w ((rectangularDiagonal m n D.factors).map φ) := by
    rw [hvq', Matrix.vecMul_vecMul, hBQq, ← Matrix.vecMul_vecMul]
  have hwi : ∀ i : Fin m, w i = ((Matrix.vecMul v Q) ⟨i.val, lt_of_lt_of_le i.2 D.rows_le_cols⟩ : ℚ) := by
    intro i
    have := congrFun hw1 ⟨i.val, lt_of_lt_of_le i.2 D.rows_le_cols⟩
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, rectangularDiagonal] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true, h1 i] at this
      simp only [Matrix.vecMul, dotProduct]; push_cast
      simpa [φ] using this.symm
    · intro b _ hb
      have : ¬ (b.val = i.val) := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  have hqw : q = Matrix.vecMul w (P.map φ) := by
    rw [hw, Matrix.vecMul_vecMul, hPPq, Matrix.vecMul_one]
  set c : Fin m → ℤ := Matrix.vecMul (fun i : Fin m => (Matrix.vecMul v Q) ⟨i.val, lt_of_lt_of_le i.2 D.rows_le_cols⟩) P
  have hqc : q = fun k => (c k : ℚ) := by
    rw [hqw]; funext k
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hwi, c]
    push_cast; simp [φ]
  rw [hqc] at hvq'
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
  funext j
  have := congrFun hvq' j
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ((∑ k, c k * B k j : ℤ) : ℚ) = (v j : ℚ) := by push_cast; simpa [φ] using this.symm
  exact_mod_cast this


theorem g64n_rrb (alpha : Fin n → K) (B S : Matrix (Fin m) (Fin n) ℤ)
    (M N : Matrix (Fin m) (Fin m) ℚ)
    (h1 : B.map (Int.castRingHom ℚ) = M * S.map (Int.castRingHom ℚ))
    (h2 : S.map (Int.castRingHom ℚ) = N * B.map (Int.castRingHom ℚ)) (h3 : N * M = 1)
    (hB : RationalRowsBasis alpha B) : RationalRowsBasis alpha S := by
  set Bq := B.map (Int.castRingHom ℚ)
  set Sq := S.map (Int.castRingHom ℚ)
  have eB : (fun i j => (B i j : ℚ)) = Bq := rfl
  have eS : (fun i j => (S i j : ℚ)) = Sq := rfl
  have hrow : ∀ (X Y : Matrix (Fin m) (Fin n) ℚ) (L : Matrix (Fin m) (Fin m) ℚ), X = L * Y →
      ∀ i, X i ∈ Submodule.span ℚ (Set.range Y) := by
    intro X Y L h i
    have : X i = ∑ k, L i k • Y k := by
      rw [h]; funext j; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  unfold RationalRowsBasis at hB ⊢
  rw [eB] at hB; rw [eS]
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.mpr ?_
    intro g hg
    have hg' : Matrix.vecMul g Sq = 0 := by rw [g64n_vecMul_eq]; exact hg
    have : Matrix.vecMul (Matrix.vecMul g N) Bq = 0 := by
      rw [Matrix.vecMul_vecMul, ← h2, hg']
    rw [g64n_vecMul_eq] at this
    have h0 := Fintype.linearIndependent_iff.mp hB.1 _ this
    have hz : Matrix.vecMul g N = 0 := funext h0
    have : g = Matrix.vecMul (Matrix.vecMul g N) M := by
      rw [Matrix.vecMul_vecMul, h3, Matrix.vecMul_one]
    rw [this, hz, Matrix.zero_vecMul]; intro i; rfl
  · rw [← hB.2]
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hrow Sq Bq N h2 i
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hrow Bq Sq M h1 i

theorem g64n_rowsZ' (alpha : Fin n → K) (S : Matrix (Fin m) (Fin n) ℤ)
    (hB : RationalRowsBasis alpha S) (i : Fin m) : S i ∈ relationKernel ℤ alpha :=
  g64n_rowsZ alpha S hB i

variable {F : Type*} [Field F] [hcharF : CharZero F] [Algebra F K] [hclosureF : IsAlgClosure F K]

section

include hcharF hclosureF

theorem solution (alpha : Fin n → K)
    (B : Matrix (Fin m) (Fin n) ℤ) (hB : RationalRowsBasis alpha B) (D : SmithData B) :
    (∀ i, saturationMatrix D i ∈ relationKernel ℤ alpha) ∧
    RationalRowsBasis alpha (saturationMatrix D) ∧
    ((D.P : Matrix (Fin m) (Fin m) ℤ) * saturationMatrix D *
      (D.Q : Matrix (Fin n) (Fin n) ℤ) = rectangularDiagonal m n (fun _ => 1)) ∧
    IntegerRowsBasis alpha (saturationMatrix D) := by
  set P : Matrix (Fin m) (Fin m) ℤ := (D.P : Matrix (Fin m) (Fin m) ℤ)
  set Pinv : Matrix (Fin m) (Fin m) ℤ := ((D.P⁻¹ : (Matrix (Fin m) (Fin m) ℤ)ˣ) : Matrix (Fin m) (Fin m) ℤ)
  set Q : Matrix (Fin n) (Fin n) ℤ := (D.Q : Matrix (Fin n) (Fin n) ℤ)
  set Qinv : Matrix (Fin n) (Fin n) ℤ := ((D.Q⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ)
  have hPP : P * Pinv = 1 := D.P.mul_inv
  have hPP' : Pinv * P = 1 := D.P.inv_mul
  have hQQ : Qinv * Q = 1 := D.Q.inv_mul
  have hQQ' : Q * Qinv = 1 := D.Q.mul_inv
  set R1 := rectangularDiagonal m n (fun _ => 1)
  set S := saturationMatrix D
  have hS : S = Pinv * R1 * Qinv := by simp only [S, saturationMatrix, Pinv, R1, Qinv, Matrix.coe_units_inv]
  have h3 : P * S * Q = R1 := by
    rw [hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hQQ,
      Matrix.mul_one]
  have hBexp : B = Pinv * rectangularDiagonal m n D.factors * Qinv := by
    rw [← D.equation]
    simp only [P, Pinv, Q, Qinv, Matrix.mul_assoc]
    rw [hQQ', Matrix.mul_one, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  have hR : rectangularDiagonal m n D.factors = Matrix.diagonal D.factors * R1 := by
    funext i j
    simp [R1, rectangularDiagonal, Matrix.diagonal_mul]
  let φ := Int.castRingHom ℚ
  let dq : Fin m → ℚ := fun i => (D.factors i : ℚ)
  have hdq : ∀ i, dq i ≠ 0 := fun i => by simp only [dq]; exact_mod_cast (D.positive i).ne'
  let M : Matrix (Fin m) (Fin m) ℚ := Pinv.map φ * Matrix.diagonal dq * P.map φ
  let N : Matrix (Fin m) (Fin m) ℚ := Pinv.map φ * Matrix.diagonal (fun i => (dq i)⁻¹) * P.map φ
  have hPq : P.map φ * Pinv.map φ = 1 := by rw [← Matrix.map_mul, hPP, Matrix.map_one] <;> simp
  have hdiag : (Matrix.diagonal D.factors).map φ = Matrix.diagonal dq := by
    funext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, dq, φ]
  have e1 : B.map φ = M * S.map φ := by
    simp only [M]
    rw [hBexp, hR, hS]
    simp only [Matrix.map_mul, hdiag, Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (P.map φ), hPq, Matrix.one_mul]
  have e2 : S.map φ = N * B.map φ := by
    simp only [N]
    rw [hBexp, hR, hS]
    simp only [Matrix.map_mul, hdiag, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc (P.map φ), hPq, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have : (fun i => (dq i)⁻¹ * dq i) = fun _ => (1 : ℚ) := funext fun i => inv_mul_cancel₀ (hdq i)
    rw [this, Matrix.diagonal_one]  -- may need adjusting
    simp
  have e3 : N * M = 1 := by
    simp only [N, M, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P.map φ) (Pinv.map φ), hPq, Matrix.one_mul, ← Matrix.mul_assoc
      (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have : (fun i => (dq i)⁻¹ * dq i) = fun _ => (1 : ℚ) := funext fun i => inv_mul_cancel₀ (hdq i)
    rw [this, Matrix.diagonal_one, Matrix.one_mul, ← Matrix.map_mul, hPP', Matrix.map_one] <;> simp
  have hSr : RationalRowsBasis alpha S := g64n_rrb alpha B S M N e1 e2 e3 hB
  let D' : SmithData S :=
    { rows_le_cols := D.rows_le_cols, P := D.P, Q := D.Q, factors := fun _ => 1,
      positive := fun _ => one_pos, divides := fun _ _ _ => dvd_refl _, equation := h3 }
  exact ⟨g64n_rowsZ alpha S hSr, hSr, h3, g64n_bwd alpha S hSr D' (fun _ => rfl)⟩

end

end Relations
