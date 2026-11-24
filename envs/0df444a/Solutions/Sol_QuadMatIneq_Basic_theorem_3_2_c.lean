-- Prove2me | solution 1 for QuadMatIneq.Basic.theorem_3_2_c
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:41:28.369017+00:00
-- url     : https://prove2.me/submissions/a9fd7388-97f3-4c38-8d03-f3201a16763d

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

open Matrix QuadMatIneq.Basic

namespace QMIAux

theorem spec_real {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ) (hD : D.IsHermitian) :
    ∃ U : Matrix κ κ ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ D = U * diagonal hD.eigenvalues * Uᵀ := by
  refine ⟨(hD.eigenvectorUnitary : Matrix κ κ ℝ), ?_, ?_, ?_⟩
  · have h := Unitary.coe_star_mul_self hD.eigenvectorUnitary
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := Unitary.coe_star_mul_self hD.eigenvectorUnitary
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact mul_eq_one_comm.mp h
  · have h := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    try rw [Unitary.coe_star] at h
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    have e : (RCLike.ofReal ∘ hD.eigenvalues : κ → ℝ) = hD.eigenvalues := by
      ext i; simp
    rw [e] at h
    exact h

theorem exists_mp {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian) : ∃ X, IsMoorePenrose D X := by
  obtain ⟨U, hU1, hU2, hDU⟩ := spec_real D hD
  generalize hD.eigenvalues = e at hDU
  have key : ∀ a b : Matrix κ κ ℝ, (U * a * Uᵀ) * (U * b * Uᵀ) = U * (a * b) * Uᵀ := by
    intro a b
    calc (U * a * Uᵀ) * (U * b * Uᵀ) = U * a * (Uᵀ * U) * b * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (a * b) * Uᵀ := by rw [hU1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have tr : ∀ d : κ → ℝ, (U * diagonal d * Uᵀ)ᵀ = U * diagonal d * Uᵀ := by
    intro d
    rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have d1 : diagonal e * diagonal (fun i => (e i)⁻¹) * diagonal e = diagonal e := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : e i = 0 <;> simp [h]
  have d2 : diagonal (fun i => (e i)⁻¹) * diagonal e * diagonal (fun i => (e i)⁻¹)
      = diagonal (fun i => (e i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i
    by_cases h : e i = 0 <;> simp [h]
  subst hDU
  refine ⟨U * diagonal (fun i => (e i)⁻¹) * Uᵀ, ?_, ?_, ?_, ?_⟩
  · rw [key, key, d1]
  · rw [key, key, d2]
  · rw [key, diagonal_mul_diagonal, tr]
  · rw [key, diagonal_mul_diagonal, tr]

theorem pinv_spec {κ : Type*} [Fintype κ] [DecidableEq κ] (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian) : IsMoorePenrose D (pinv D) := by
  unfold pinv
  exact Classical.epsilon_spec (exists_mp D hD)

theorem qmiForm_expand {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₁ + Zᵀ * P.toBlocks₂₂ * Z := by
  have h : qmiForm P Z = (fromRows (1 : Matrix ι ι ℝ) Z)ᵀ *
      (fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ *
        fromRows (1 : Matrix ι ι ℝ) Z) := by
    rw [fromBlocks_toBlocks, ← Matrix.mul_assoc]; rfl
  rw [h, fromBlocks_mul_fromRows, transpose_fromRows, fromCols_mul_fromRows]
  simp only [Matrix.mul_one, transpose_one, Matrix.one_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem core {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D X : Matrix κ κ ℝ) (hDt : Dᵀ = D)
    (h1 : D * X * D = D) (hker : ∀ v : κ → ℝ, D *ᵥ v = 0 → B *ᵥ v = 0) (Z : Matrix κ ι ℝ) :
    A + B * Z + Zᵀ * Bᵀ + Zᵀ * D * Z
      = A - B * X * Bᵀ + (Z + X * Bᵀ)ᵀ * D * (Z + X * Bᵀ) := by
  have hDX : D * (1 - X * D) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, sub_self]
  have hB0 : B * (1 - X * D) = 0 := by
    ext i j
    have hv : D *ᵥ (fun k => (1 - X * D) k j) = 0 := by
      ext i'
      have := congrFun (congrFun hDX i') j
      exact this
    have := congrFun (hker _ hv) i
    exact this
  have hE1 : B * (X * D) = B := by
    have := hB0
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hE3 : D * (Xᵀ * Bᵀ) = Bᵀ := by
    have := congrArg transpose hE1
    rw [transpose_mul, transpose_mul, hDt, Matrix.mul_assoc] at this
    exact this
  have hE4 : D * (X * Bᵀ) = Bᵀ := by
    calc D * (X * Bᵀ) = D * (X * (D * (Xᵀ * Bᵀ))) := by rw [hE3]
      _ = (D * X * D) * (Xᵀ * Bᵀ) := by simp only [Matrix.mul_assoc]
      _ = Bᵀ := by rw [h1, hE3]
  have hWD : (X * Bᵀ)ᵀ * D = B := by
    have := congrArg transpose hE4
    rw [transpose_mul, hDt, transpose_transpose] at this
    exact this
  have hWDM : ∀ M : Matrix κ ι ℝ, (X * Bᵀ)ᵀ * (D * M) = B * M := fun M => by
    rw [← Matrix.mul_assoc, hWD]
  have hWB : (X * Bᵀ)ᵀ * Bᵀ = B * (X * Bᵀ) :=
    (congrArg (fun M => (X * Bᵀ)ᵀ * M) hE4).symm.trans (hWDM _)
  rw [transpose_add]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hE4, hWDM, hWB]
  abel

theorem toBlocks₂₂_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hH : P.IsHermitian) :
    P.toBlocks₂₂ᵀ = P.toBlocks₂₂ := by
  ext i j
  have := hH.apply (Sum.inr i) (Sum.inr j)
  simpa [toBlocks₂₂] using this

theorem qmi_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    ∃ W : Matrix κ ι ℝ, ∀ Z, qmiForm P Z
      = schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W) := by
  obtain ⟨hH, -, -, hker⟩ := hP
  have hDt := toBlocks₂₂_transpose P hH
  have hC : P.toBlocks₂₁ = P.toBlocks₁₂ᵀ := by
    ext i j
    have := hH.apply (Sum.inl j) (Sum.inr i)
    simpa [toBlocks₂₁, toBlocks₁₂] using this
  have hDH : P.toBlocks₂₂.IsHermitian :=
    (conjTranspose_eq_transpose_of_trivial _).trans hDt
  obtain ⟨h1, -, -, -⟩ := pinv_spec _ hDH
  refine ⟨pinv P.toBlocks₂₂ * P.toBlocks₁₂ᵀ, fun Z => ?_⟩
  unfold schur
  rw [qmiForm_expand, hC]
  exact core _ _ _ _ hDt h1 hker Z

theorem quad_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (Y : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((Yᵀ * D * Y) *ᵥ x) = (Y *ᵥ x) ⬝ᵥ (D *ᵥ (Y *ᵥ x)) := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Yᵀ,
    vecMul_transpose]

end QMIAux

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef := by
  obtain ⟨W, hQ⟩ := QMIAux.qmi_eq P hP
  obtain ⟨hH, hN, hS, hker⟩ := hP
  have hDt := QMIAux.toBlocks₂₂_transpose P hH
  have hSt : (schur P)ᵀ = schur P := (conjTranspose_eq_transpose_of_trivial _).symm.trans hS.1
  constructor
  · rintro ⟨Z0, hZ0⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hD0, hSn⟩ := hcon
    obtain ⟨x, hx0, hSx⟩ : ∃ x : ι → ℝ, x ≠ 0 ∧ schur P *ᵥ x = 0 := by
      by_contra h
      push Not at h
      apply hSn
      refine PosDef.of_dotProduct_mulVec_pos hS.1 (fun x hx => ?_)
      have h1 := hS.dotProduct_mulVec_nonneg x
      rcases h1.lt_or_eq with h2 | h2
      · exact h2
      · exact absurd ((hS.dotProduct_mulVec_zero_iff x).mp h2.symm) (h x hx)
    have hkey : ∀ Z ∈ ZSet P, P.toBlocks₂₂ *ᵥ ((Z + W) *ᵥ x) = 0 := by
      intro Z hZ
      have h0 : 0 ≤ star x ⬝ᵥ (qmiForm P Z *ᵥ x) :=
        (show (qmiForm P Z).PosSemidef from hZ).dotProduct_mulVec_nonneg x
      rw [hQ, add_mulVec, hSx, zero_add, star_trivial, QMIAux.quad_eq] at h0
      have h1 := hN.dotProduct_mulVec_nonneg ((Z + W) *ᵥ x)
      rw [star_trivial, neg_mulVec, dotProduct_neg] at h1
      have h2 : star ((Z + W) *ᵥ x) ⬝ᵥ ((-P.toBlocks₂₂) *ᵥ ((Z + W) *ᵥ x)) = 0 := by
        rw [star_trivial, neg_mulVec, dotProduct_neg]; linarith
      have h3 := (hN.dotProduct_mulVec_zero_iff _).mp h2
      rwa [neg_mulVec, neg_eq_zero] at h3
    obtain ⟨u, hu⟩ : ∃ u : κ → ℝ, P.toBlocks₂₂ *ᵥ u ≠ 0 := by
      by_contra h
      push Not at h
      apply hD0
      ext i j
      have := congrFun (h (Pi.single j 1)) i
      simpa using this
    have hxx : x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_self_eq_zero.mp h)
    have hcont : Continuous (fun t : ℝ => Z0 + t • vecMulVec u x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hopen : IsOpen ((fun t : ℝ => Z0 + t • vecMulVec u x) ⁻¹' interior (ZSet P)) :=
      isOpen_interior.preimage hcont
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa using hZ0)
    have ht : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hmem : Z0 + (ε / 2) • vecMulVec u x ∈ ZSet P := interior_subset (hball ht)
    have e1 := hkey _ hmem
    have e0 := hkey _ (interior_subset hZ0)
    have hsplit : (Z0 + (ε / 2) • vecMulVec u x + W) *ᵥ x
        = (Z0 + W) *ᵥ x + (ε / 2) • ((x ⬝ᵥ x) • u) := by
      rw [add_right_comm, add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
    rw [hsplit, mulVec_add, e0, zero_add, mulVec_smul, mulVec_smul] at e1
    apply hu
    have h5 : (ε / 2 * (x ⬝ᵥ x)) • (P.toBlocks₂₂ *ᵥ u) = 0 := by
      rw [mul_smul]; exact e1
    rcases smul_eq_zero.mp h5 with h | h
    · exact absurd h (mul_ne_zero (by positivity) hxx)
    · exact h
  · rintro (h0 | hPD)
    · refine ⟨0, ?_⟩
      have hU : ZSet P = Set.univ := by
        ext Z
        simp only [Set.mem_univ, iff_true]
        show (qmiForm P Z).PosSemidef
        rw [hQ, h0, Matrix.mul_zero, Matrix.zero_mul, add_zero]
        exact hS
      rw [hU, interior_univ]; trivial
    · let f : Matrix κ ι ℝ × (ι → ℝ) → ℝ := fun p =>
        p.2 ⬝ᵥ ((schur P + (p.1 + W)ᵀ * P.toBlocks₂₂ * (p.1 + W)) *ᵥ p.2)
      have hf : Continuous f :=
        Continuous.dotProduct continuous_snd
          (Continuous.matrix_mulVec
            (continuous_const.add
              (((continuous_fst.add continuous_const).matrix_transpose.matrix_mul
                continuous_const).matrix_mul (continuous_fst.add continuous_const)))
            continuous_snd)
      have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere _ _
      have hn : IsOpen (f ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hf
      have hsub : ({-W} : Set (Matrix κ ι ℝ)) ×ˢ Metric.sphere (0 : ι → ℝ) 1
          ⊆ f ⁻¹' Set.Ioi 0 := by
        rintro ⟨Z, x⟩ ⟨hZ, hx⟩
        have hZ' : Z = -W := hZ
        have hx0 : x ≠ 0 := by
          rintro rfl
          simp at hx
        show 0 < x ⬝ᵥ ((schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W)) *ᵥ x)
        rw [hZ', neg_add_cancel, Matrix.mul_zero, add_zero]
        have := hPD.dotProduct_mulVec_pos hx0
        rwa [star_trivial] at this
      obtain ⟨U, V, hU, hV, hsU, hsV, hUV⟩ :=
        generalized_tube_lemma isCompact_singleton hK hn hsub
      refine ⟨-W, mem_interior.mpr ⟨U, ?_, hU, hsU (Set.mem_singleton _)⟩⟩
      intro Z hZ
      show (qmiForm P Z).PosSemidef
      rw [hQ]
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
      · show (schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W))ᴴ = _
        rw [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_mul, transpose_mul,
          transpose_transpose, hDt, hSt, ← Matrix.mul_assoc]
      · rw [star_trivial]
        by_cases hx : x = 0
        · rw [hx]; simp
        · have hc : 0 < ‖x‖ := norm_pos_iff.mpr hx
          have hx' : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : ι → ℝ) 1 := by
            rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
              inv_mul_cancel₀ hc.ne']
          have hpos : 0 < f (Z, ‖x‖⁻¹ • x) := hUV (Set.mk_mem_prod hZ (hsV hx'))
          have hscale : f (Z, ‖x‖⁻¹ • x) = ‖x‖⁻¹ * ‖x‖⁻¹ *
              (x ⬝ᵥ ((schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W)) *ᵥ x)) := by
            show (‖x‖⁻¹ • x) ⬝ᵥ ((schur P + (Z + W)ᵀ * P.toBlocks₂₂ * (Z + W)) *ᵥ (‖x‖⁻¹ • x))
              = _
            rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
            ring
          rw [hscale] at hpos
          have h2 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ := by positivity
          exact le_of_lt ((mul_pos_iff_of_pos_left h2).mp hpos)
