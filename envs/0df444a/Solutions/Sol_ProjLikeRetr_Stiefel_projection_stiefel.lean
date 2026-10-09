-- Prove2me | solution 1 for ProjLikeRetr.Stiefel.projection_stiefel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:57:48.292443+00:00
-- url     : https://prove2.me/submissions/c59ba5f6-6fbb-48ca-8425-74e2e0ca6d8d

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ProjLikeRetr_Stiefel_SVD

set_option autoImplicit false

open scoped Matrix Matrix.Norms.Frobenius

namespace PBE1A43D2

open ProjLikeRetr.Stiefel Matrix

lemma frob_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j * A i j := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  norm_num
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sq]

lemma frob_sq_trace {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : ‖A‖ ^ 2 = (Aᵀ * A).trace := by
  rw [frob_sq, Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.mul_apply]

/-- copy of our accepted dist_sq_stiefel (5c936dc8) -/
lemma dist_sq {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℝ) (hY : Y ∈ stiefel n m) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + (m : ℝ) - 2 * (Yᵀ * X).trace := by
  have hY' : Yᵀ * Y = 1 := hY
  have hm : (∑ i, ∑ j, Y i j * Y i j) = (m : ℝ) := by
    have := congrArg Matrix.trace hY'
    rw [Matrix.trace_one, Fintype.card_fin] at this
    rw [← this, Matrix.trace, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply]
  have ht : (Yᵀ * X).trace = ∑ i, ∑ j, Y i j * X i j := by
    rw [Matrix.trace, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply]
  rw [frob_sq, frob_sq, ht, ← hm]
  simp only [Matrix.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma orth_tt {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (h : U ∈ Matrix.orthogonalGroup (Fin k) ℝ) : Uᵀ * U = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma orth_t {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (h : U ∈ Matrix.orthogonalGroup (Fin k) ℝ) : U * Uᵀ = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma diag_sum {n m : ℕ} (hmn : m ≤ n) (S : Matrix (Fin n) (Fin m) ℝ)
    (hS : ∀ i j, i.val ≠ j.val → S i j = 0) (A : Matrix (Fin m) (Fin n) ℝ) :
    (A * S).trace = ∑ j : Fin m, A j (Fin.castLE hmn j) * S (Fin.castLE hmn j) j := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_eq_single (Fin.castLE hmn j) ?_ ?_
  · intro i _ hi
    have : i.val ≠ j.val := fun h => hi (Fin.ext (by simp [h]))
    simp [hS i j this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma entry_le_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : A * Aᵀ = 1)
    (j : Fin m) (i : Fin n) : A j i ≤ 1 := by
  have h1 : ∑ k, A j k * A j k = 1 := by
    have := congrFun (congrFun h j) j
    simpa [Matrix.mul_apply] using this
  have h2 : A j i * A j i ≤ ∑ k, A j k * A j k :=
    Finset.single_le_sum (f := fun k => A j k * A j k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  nlinarith

lemma rect_tt {n m : ℕ} (hmn : m ≤ n) :
    (rectId n m)ᵀ * rectId n m = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rectId,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castLE hmn i)]
  · by_cases hij : i = j
    · subst hij; simp
    · have : ¬ ((Fin.castLE hmn i).val = j.val) := by
        simpa [Fin.ext_iff] using hij
      simp only [this, if_false, mul_zero]
      simp only [Fin.ext_iff] at hij
      simp [Fin.ext_iff, hij]
  · intro k _ hk
    have : ¬ (k.val = i.val) := fun h => hk (Fin.ext (by simp [h]))
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma frame_mem {n m : ℕ} (hmn : m ≤ n) (U : Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hV : V ∈ Matrix.orthogonalGroup (Fin m) ℝ) : frameOfSVD U V ∈ stiefel n m := by
  show (frameOfSVD U V)ᵀ * frameOfSVD U V = 1
  unfold frameOfSVD
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, orth_tt hU, Matrix.one_mul, ← Matrix.mul_assoc (rectId n m)ᵀ,
    rect_tt hmn, Matrix.one_mul, orth_t hV]

/-- σ_m(X̄) = 1 on the Stiefel manifold. -/
lemma sv_stiefel {n m : ℕ} (hm : 0 < m) (Xbar : Matrix (Fin n) (Fin m) ℝ)
    (hXbar : Xbar ∈ stiefel n m) : ProjLikeRetr.FixedRank.sv Xbar m = 1 := by
  have hX' : Xbarᵀ * Xbar = 1 := hXbar
  unfold ProjLikeRetr.FixedRank.sv
  set T := Matrix.toEuclideanLin Xbar with hT
  have hid : LinearMap.adjoint T ∘ₗ T = LinearMap.id := by
    rw [hT, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    apply LinearMap.ext
    intro v
    change WithLp.toLp 2 (Xbarᴴ *ᵥ (Xbar *ᵥ WithLp.ofLp v)) = v
    rw [Matrix.mulVec_mulVec, Matrix.conjTranspose_eq_transpose_of_trivial, hX',
      Matrix.one_mulVec]
  have hfr : m - 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [finrank_euclideanSpace_fin]; omega
  have hev := T.hasEigenvalue_adjoint_comp_self_sq_singularValues hfr
  rw [hid] at hev
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hv2 : v = T.singularValues (m - 1) ^ 2 • v := by
    simpa using hv.apply_eq_smul
  have h1 : (T.singularValues (m - 1) ^ 2 - 1) • v = 0 := by
    rw [sub_smul, ← hv2, one_smul, sub_self]
  have h2 : T.singularValues (m - 1) ^ 2 = 1 := by
    rcases smul_eq_zero.mp h1 with h | h
    · linarith
    · exact absurd h hv.2
  have h3 := T.singularValues_nonneg (m - 1)
  nlinarith

/-- S1: every diagonal entry of an SVD of X is positive. -/
lemma svd_diag_pos {n m : ℕ} (hmn : m ≤ n) (hm : 0 < m)
    (Xbar X : Matrix (Fin n) (Fin m) ℝ) (hXbar : Xbar ∈ stiefel n m)
    (hX : ‖X - Xbar‖ < ProjLikeRetr.FixedRank.sv Xbar m)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) :
    ∀ k : Fin m, 0 < S (Fin.castLE hmn k) k := by
  obtain ⟨hU, hV, hoff, hnn, -, hXe⟩ := hsvd
  rw [sv_stiefel hm Xbar hXbar] at hX
  have hX' : Xbarᵀ * Xbar = 1 := hXbar
  intro k
  rcases (hnn (Fin.castLE hmn k) k (by simp)).lt_or_eq with h | h
  · exact h
  exfalso
  let e : Matrix (Fin m) (Fin 1) ℝ := Matrix.of fun i _ => if i = k then 1 else 0
  have hee : eᵀ * e = 1 := by
    ext a b
    simp [e, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim a b]
  have hSe : S * e = 0 := by
    ext i j
    simp only [e, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hik : i.val = k.val
    · have : i = Fin.castLE hmn k := Fin.ext (by simp [hik])
      rw [this, ← h]
    · exact hoff i k hik
  set w := V * e with hw
  have hww : wᵀ * w = 1 := by
    rw [hw, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, orth_tt hV,
      Matrix.one_mul, hee]
  have hXw : X * w = 0 := by
    rw [hXe, hw, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, orth_tt hV,
      Matrix.one_mul, hSe, Matrix.mul_zero]
  have hn1 : ‖w‖ = 1 := by
    have := frob_sq_trace w
    rw [hww, Matrix.trace_one, Fintype.card_fin, Nat.cast_one] at this
    nlinarith [norm_nonneg w]
  have hn2 : ‖(X - Xbar) * w‖ = 1 := by
    have h' : (X - Xbar) * w = -(Xbar * w) := by
      rw [Matrix.sub_mul, hXw, zero_sub]
    rw [h', norm_neg]
    have := frob_sq_trace (Xbar * w)
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Xbarᵀ, hX', Matrix.one_mul,
      hww, Matrix.trace_one, Fintype.card_fin, Nat.cast_one] at this
    nlinarith [norm_nonneg (Xbar * w)]
  have := Matrix.frobenius_norm_mul (X - Xbar) w
  rw [hn1, hn2, mul_one] at this
  linarith

/-- S2: equality in the trace bound forces Y = U E Vᵀ. -/
lemma eq_frame {n m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) (hpos : ∀ i : Fin m, 0 < S (Fin.castLE hmn i) i)
    (Y : Matrix (Fin n) (Fin m) ℝ) (hY : Y ∈ stiefel n m)
    (htr : (Yᵀ * X).trace = ∑ i : Fin m, S (Fin.castLE hmn i) i) :
    Y = frameOfSVD U V := by
  obtain ⟨hU, hV, hoff, hnn, -, hXe⟩ := hsvd
  have hY' : Yᵀ * Y = 1 := hY
  set A := Vᵀ * Yᵀ * U with hAdef
  have hA : A * Aᵀ = 1 := by
    rw [hAdef]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, orth_t hU, Matrix.one_mul, ← Matrix.mul_assoc Yᵀ Y, hY',
      Matrix.one_mul, orth_tt hV]
  have htr2 : (Yᵀ * X).trace = (A * S).trace := by
    rw [hXe, hAdef]
    calc (Yᵀ * (U * S * Vᵀ)).trace = ((Yᵀ * U * S) * Vᵀ).trace := by
            simp only [Matrix.mul_assoc]
      _ = (Vᵀ * (Yᵀ * U * S)).trace := Matrix.trace_mul_comm _ _
      _ = ((Vᵀ * Yᵀ * U) * S).trace := by simp only [Matrix.mul_assoc]
  rw [htr2, diag_sum hmn S hoff] at htr
  have hdiag : ∀ j : Fin m, A j (Fin.castLE hmn j) = 1 := by
    have hsum : ∑ j : Fin m, (1 - A j (Fin.castLE hmn j)) * S (Fin.castLE hmn j) j = 0 := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      linarith
    have hnn' : ∀ j ∈ Finset.univ, 0 ≤ (1 - A j (Fin.castLE hmn j)) * S (Fin.castLE hmn j) j :=
      fun j _ => mul_nonneg (by linarith [entry_le_one A hA j (Fin.castLE hmn j)]) (hpos j).le
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hsum j (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h (hpos j).ne'
  have hE : ∀ i j, i.val ≠ j.val → rectId n m i j = 0 := by
    intro i j hij; simp [rectId, hij]
  have htrF : (Yᵀ * frameOfSVD U V).trace = (m : ℝ) := by
    have : (Yᵀ * frameOfSVD U V).trace = (A * rectId n m).trace := by
      unfold frameOfSVD
      rw [hAdef]
      calc (Yᵀ * (U * rectId n m * Vᵀ)).trace = ((Yᵀ * U * rectId n m) * Vᵀ).trace := by
              simp only [Matrix.mul_assoc]
        _ = (Vᵀ * (Yᵀ * U * rectId n m)).trace := Matrix.trace_mul_comm _ _
        _ = ((Vᵀ * Yᵀ * U) * rectId n m).trace := by simp only [Matrix.mul_assoc]
    rw [this, diag_sum hmn _ hE]
    simp [hdiag, rectId]
  have hF := frame_mem hmn U V hU hV
  have h0 := dist_sq (0 : Matrix (Fin n) (Fin m) ℝ) _ hF
  simp only [zero_sub, norm_neg, norm_zero, Matrix.mul_zero, Matrix.trace_zero] at h0
  have h1 := dist_sq (frameOfSVD U V) Y hY
  rw [htrF] at h1
  have h2 : ‖frameOfSVD U V - Y‖ ^ 2 = 0 := by
    rw [h1]
    norm_num at h0 ⊢
    linarith
  have := sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))
  exact this.symm

/-- S3: the polar factor. -/
lemma polar_of_svd {n m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) (hpos : ∀ i : Fin m, 0 < S (Fin.castLE hmn i) i) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, P.PosDef ∧ X = frameOfSVD U V * P := by
  obtain ⟨hU, hV, hoff, hnn, -, hXe⟩ := hsvd
  let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal fun j => S (Fin.castLE hmn j) j
  have hED : rectId n m * D = S := by
    ext i j
    simp only [D, Matrix.mul_diagonal, rectId, Matrix.of_apply]
    by_cases hij : i.val = j.val
    · have : i = Fin.castLE hmn j := Fin.ext (by simp [hij])
      subst this
      simp
    · simp [hij, hoff i j hij]
  have hD : D.PosDef := Matrix.PosDef.diagonal hpos
  refine ⟨V * D * Vᵀ, ?_, ?_⟩
  · have := hD.mul_mul_conjTranspose_same (B := V) ?_
    · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    · intro x y hxy
      have := congrArg (fun z => Matrix.vecMul z Vᵀ) hxy
      simp only [Matrix.vecMul_vecMul, orth_t hV, Matrix.vecMul_one] at this
      exact this
  · rw [hXe]
    unfold frameOfSVD
    rw [← hED]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, orth_tt hV, Matrix.one_mul]

open scoped MatrixOrder in
lemma sq_inj {m : ℕ} (P₁ P₂ : Matrix (Fin m) (Fin m) ℝ)
    (hP₁ : P₁.PosSemidef) (hP₂ : P₂.PosSemidef) (h : P₁ * P₁ = P₂ * P₂) : P₁ = P₂ :=
  (CFC.sq_eq_sq_iff P₁ P₂ hP₁.nonneg hP₂.nonneg).mp (by simpa [sq] using h)

lemma gram {n m : ℕ} (W : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ stiefel n m)
    (hP : P.PosSemidef) : (W * P)ᵀ * (W * P) = P * P := by
  have hW' : Wᵀ * W = 1 := hW
  have hPt : Pᵀ = P := by
    have := hP.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  rw [Matrix.transpose_mul, hPt, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW', Matrix.one_mul]

end PBE1A43D2

open RandomGradFree.Nonsmooth ProjLikeRetr.Stiefel Matrix Matrix.Norms.Frobenius in
theorem solution {n m : ℕ} (hmn : m ≤ n) (hm : 0 < m)
    (Xbar X : Matrix (Fin n) (Fin m) ℝ) (hXbar : Xbar ∈ stiefel n m)
    (hX : ‖X - Xbar‖ < ProjLikeRetr.FixedRank.sv Xbar m)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) :
    {Y | IsMetricProjection (stiefel n m) X Y} = {frameOfSVD U V} ∧
      (∀ (W : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin m) (Fin m) ℝ),
        W ∈ stiefel n m → P.PosDef → X = W * P → W = frameOfSVD U V) ∧
      ∃ P : Matrix (Fin m) (Fin m) ℝ, P.PosDef ∧ X = frameOfSVD U V * P := by
  have hpos := PBE1A43D2.svd_diag_pos hmn hm Xbar X hXbar hX U S V hsvd
  have hsvd' := hsvd
  obtain ⟨hU, hV, hoff, hnn, -, hXe⟩ := hsvd'
  have hF := PBE1A43D2.frame_mem hmn U V hU hV
  -- trace bound (9ed9c518, reproved inline)
  have hbound : ∀ Y ∈ stiefel n m, (Yᵀ * X).trace ≤ ∑ i : Fin m, S (Fin.castLE hmn i) i := by
    intro Y hY
    have hY' : Yᵀ * Y = 1 := hY
    have htr : (Yᵀ * X).trace = ((Vᵀ * Yᵀ * U) * S).trace := by
      rw [hXe]
      calc (Yᵀ * (U * S * Vᵀ)).trace = ((Yᵀ * U * S) * Vᵀ).trace := by
              simp only [Matrix.mul_assoc]
        _ = (Vᵀ * (Yᵀ * U * S)).trace := Matrix.trace_mul_comm _ _
        _ = ((Vᵀ * Yᵀ * U) * S).trace := by simp only [Matrix.mul_assoc]
    rw [htr, PBE1A43D2.diag_sum hmn S hoff]
    have hA : (Vᵀ * Yᵀ * U) * (Vᵀ * Yᵀ * U)ᵀ = 1 := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᵀ, PBE1A43D2.orth_t hU, Matrix.one_mul,
        ← Matrix.mul_assoc Yᵀ Y, hY', Matrix.one_mul, PBE1A43D2.orth_tt hV]
    apply Finset.sum_le_sum
    intro j _
    have h1 := PBE1A43D2.entry_le_one _ hA j (Fin.castLE hmn j)
    have h2 : 0 ≤ S (Fin.castLE hmn j) j := hnn _ _ (by simp)
    nlinarith
  have hFtr : ((frameOfSVD U V)ᵀ * X).trace = ∑ i : Fin m, S (Fin.castLE hmn i) i := by
    rw [hXe]
    unfold frameOfSVD
    have : ((U * rectId n m * Vᵀ)ᵀ * (U * S * Vᵀ)).trace = ((rectId n m)ᵀ * S).trace := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, PBE1A43D2.orth_tt hU, Matrix.one_mul, Matrix.trace_mul_comm V]
      simp only [Matrix.mul_assoc, PBE1A43D2.orth_tt hV, Matrix.mul_one]
    rw [this, PBE1A43D2.diag_sum hmn S hoff]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [rectId]
  obtain ⟨PF, hPF, hXPF⟩ := PBE1A43D2.polar_of_svd hmn X U S V hsvd hpos
  refine ⟨?_, ?_, ⟨PF, hPF, hXPF⟩⟩
  · ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hY, hmin⟩
      have h1 := hmin _ hF
      have h2 : ‖X - Y‖ ^ 2 ≤ ‖X - frameOfSVD U V‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [PBE1A43D2.dist_sq X Y hY, PBE1A43D2.dist_sq X _ hF, hFtr] at h2
      have h3 := hbound Y hY
      exact PBE1A43D2.eq_frame hmn X U S V hsvd hpos Y hY (by linarith)
    · rintro rfl
      refine ⟨hF, fun W hW => ?_⟩
      have h2 : ‖X - frameOfSVD U V‖ ^ 2 ≤ ‖X - W‖ ^ 2 := by
        rw [PBE1A43D2.dist_sq X W hW, PBE1A43D2.dist_sq X _ hF, hFtr]
        linarith [hbound W hW]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · intro W P hW hP hXW
    have hPP : P = PF := by
      apply PBE1A43D2.sq_inj P PF hP.posSemidef hPF.posSemidef
      rw [← PBE1A43D2.gram W P hW hP.posSemidef, ← PBE1A43D2.gram _ PF hF hPF.posSemidef,
        ← hXW, ← hXPF]
    subst hPP
    have hu : IsUnit P := hP.isUnit
    have := congrArg (fun Z => Z * P⁻¹) (hXW.symm.trans hXPF)
    simp only [Matrix.mul_assoc] at this
    rwa [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).mp hu), Matrix.mul_one,
      Matrix.mul_one] at this
