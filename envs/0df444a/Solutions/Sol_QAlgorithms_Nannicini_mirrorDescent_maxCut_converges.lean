-- Prove2me | solution 1 for QAlgorithms.Nannicini.mirrorDescent_maxCut_converges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:36:22.458277+00:00
-- url     : https://prove2.me/submissions/2a6df67e-5703-4aef-9141-cd0a395da677
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
import Theorems.Thm_QAlgorithms_Nannicini_mmwu_regret

set_option autoImplicit false

open QAlgorithms
open QAlgorithms.Nannicini
open QAlgorithms.SDP
open scoped ComplexConjugate ComplexOrder

namespace MirrorDescentMaxCutAux

theorem red_act_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A + B) x = act A x + act B x := by
  simp [act, Matrix.add_mulVec]

theorem red_act_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A - B) x = act A x - act B x := by
  simp [act, Matrix.sub_mulVec]

theorem red_act_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (c • A) x = c • act A x := by
  simp [act, Matrix.smul_mulVec]

theorem red_act_smul_vec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ)
    (x : EuclideanSpace ℂ ι) : act A (c • x) = c • act A x := by
  simp [act, Matrix.mulVec_smul]

theorem red_act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    act (A * B) x = act A (act B x) := by
  simp [act, Matrix.mulVec_mulVec]

theorem red_act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) x = x := by
  simp [act]

theorem sum_norm_sq_repr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (x : EuclideanSpace ℂ ι) :
    (∑ i : ι, ‖b.repr x i‖ ^ 2) = ‖x‖ ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]

theorem ascEigenvalues_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {i j : Fin (Fintype.card ι)} (hij : i ≤ j) :
    ascEigenvalues A i ≤ ascEigenvalues A j := by
  simp only [ascEigenvalues, dif_pos hA]
  exact hA.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

theorem inner_act_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) :
    inner ℂ x (act A x) =
      ((∑ i : ι, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 : ℝ) : ℂ) := by
  set b := hA.eigenvectorBasis with hbdef
  set e := hA.eigenvalues with hedef
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (e i : ℂ) • b i := by
    intro i
    change WithLp.toLp 2 (A.mulVec (b i)) = _
    rw [hbdef, hA.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hedef]
  have hAx : ∀ i, b.repr (act A x) i = (e i : ℂ) * b.repr x i := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    have hact : act A x = Matrix.toEuclideanLin A x := rfl
    rw [hact, ← hsym (b i) x, hb i, inner_smul_left]
    simp
  rw [← b.repr.inner_map_map x (act A x), PiLp.inner_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hAx i, RCLike.inner_apply]
  have hz : ∀ z : ℂ, (e i : ℂ) * z * starRingEnd ℂ z = ((e i * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    calc (e i : ℂ) * z * starRingEnd ℂ z
        = (e i : ℂ) * (z * starRingEnd ℂ z) := by ring
      _ = (e i : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = ((e i * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  exact hz (b.repr x i)

theorem re_inner_act_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) :
    (inner ℂ x (act A x)).re =
      ∑ i : ι, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
  rw [inner_act_eq_sum hA x, Complex.ofReal_re]

theorem minEigenvalue_le_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h0 : 0 < Fintype.card ι) (i : ι) :
    minEigenvalue A ≤ hA.eigenvalues i := by
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  have hmin : minEigenvalue A = ascEigenvalues A ⟨0, h0⟩ := dif_pos h0
  have hbr : ascEigenvalues A (Fin.rev (eqv.symm i)) = hA.eigenvalues i := by
    simp only [ascEigenvalues, dif_pos hA, Fin.rev_rev]
    rfl
  rw [hmin, ← hbr]
  exact ascEigenvalues_mono hA (Nat.zero_le _)

theorem minEigenvalue_le_re_inner_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h0 : 0 < Fintype.card ι)
    (x : EuclideanSpace ℂ ι) :
    minEigenvalue A * ‖x‖ ^ 2 ≤ (inner ℂ x (act A x)).re := by
  calc minEigenvalue A * ‖x‖ ^ 2
      = minEigenvalue A * ∑ i : ι, ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := by
        rw [sum_norm_sq_repr]
    _ = ∑ i : ι, minEigenvalue A * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i : ι, hA.eigenvalues i * ‖hA.eigenvectorBasis.repr x i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (minEigenvalue_le_eigenvalues hA h0 i) (sq_nonneg _)
    _ = (inner ℂ x (act A x)).re := (re_inner_act_eq_sum hA x).symm

theorem neg_specNorm_le_minEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (h0 : 0 < Fintype.card ι) :
    -specNorm A ≤ minEigenvalue A := by
  set eqv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  set i0 := eqv (Fin.rev ⟨0, h0⟩) with hi0
  set u0 := hA.eigenvectorBasis i0
  have hu0 : ‖u0‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i0
  have he0 : hA.eigenvalues i0 = minEigenvalue A := by
    have hbr : ascEigenvalues A (Fin.rev (eqv.symm i0)) = hA.eigenvalues i0 := by
      simp only [ascEigenvalues, dif_pos hA, Fin.rev_rev]
      rfl
    rw [← hbr, hi0, Equiv.symm_apply_apply, Fin.rev_rev, minEigenvalue, dif_pos h0]
  have hAu0 : (inner ℂ u0 (act A u0)).re = minEigenvalue A := by
    rw [re_inner_act_eq_sum hA u0, OrthonormalBasis.repr_self]
    have hsum : (∑ i : ι, hA.eigenvalues i * ‖EuclideanSpace.single i0 (1 : ℂ) i‖ ^ 2) =
        hA.eigenvalues i0 := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hsum, he0]
  have h1 : -(inner ℂ u0 (act A u0)).re ≤ ‖inner ℂ u0 (act A u0)‖ := by
    rw [← Complex.neg_re]
    exact (Complex.re_le_norm _).trans (by rw [norm_neg])
  have h2 : ‖inner ℂ u0 (act A u0)‖ ≤ ‖u0‖ * ‖act A u0‖ := norm_inner_le_norm _ _
  have h3 : ‖act A u0‖ ≤ specNorm A * ‖u0‖ :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A).le_opNorm u0
  simp only [hu0, one_mul, mul_one] at h2 h3
  linarith

theorem specNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    0 ≤ specNorm A :=
  norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A)

theorem specNorm_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    specNorm (0 : Matrix ι ι ℂ) = 0 := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) 0‖ = 0
  rw [map_zero, norm_zero]

theorem specNorm_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) (A : Matrix ι ι ℂ) :
    specNorm (c • A) = ‖c‖ * specNorm A := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (c • A)‖ =
    ‖c‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A‖
  rw [map_smul, norm_smul]

theorem specNorm_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    specNorm (-A) = specNorm A := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (-A)‖ =
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A‖
  rw [map_neg, norm_neg]

open scoped Matrix.Norms.Frobenius in
theorem frobNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    0 ≤ frobNorm A :=
  norm_nonneg A

open scoped Matrix.Norms.Frobenius in
theorem norm_act_le_frobNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖act A x‖ ≤ frobNorm A * ‖x‖ := by
  change ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖ ≤ ‖A‖ * ‖WithLp.toLp 2 (WithLp.ofLp x)‖
  have hmul : Matrix.replicateCol (Fin 1) (A.mulVec (WithLp.ofLp x)) =
      A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.mulVec, dotProduct]
  rw [← Matrix.frobenius_norm_replicateCol (ι := Fin 1) (A.mulVec (WithLp.ofLp x)),
    ← Matrix.frobenius_norm_replicateCol (ι := Fin 1) (WithLp.ofLp x), hmul]
  exact Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) (WithLp.ofLp x))

theorem specNorm_le_frobNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    specNorm A ≤ frobNorm A := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A‖ ≤ frobNorm A
  exact ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg A) (norm_act_le_frobNorm A)

theorem specNorm_cHat_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    specNorm (cHat A) ≤ 1 := by
  unfold cHat
  rw [specNorm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (frobNorm_nonneg A)]
  exact inv_mul_le_one_of_le₀ (specNorm_le_frobNorm A) (frobNorm_nonneg A)

theorem gibbsState_isDensityMatrix {n : ℕ} (hn : 0 < n) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : IsDensityMatrix (gibbsState H) := by
  set N : ℕ := max 1 ⌈specNorm H⌉₊
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hN_ge : specNorm H ≤ N :=
    (Nat.le_ceil (specNorm H)).trans (Nat.cast_le.mpr (le_max_right _ _))
  set M : ℕ → Matrix (Fin n) (Fin n) ℂ := fun _ => (-(((N : ℝ)⁻¹ : ℝ) : ℂ)) • H
  have hMherm : ∀ t ∈ Finset.Icc 1 N, (M t).IsHermitian := by
    intro t _
    dsimp [M]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  have hMnorm : ∀ t ∈ Finset.Icc 1 N, specNorm (M t) ≤ 1 := by
    intro t _
    dsimp [M]
    rw [specNorm_smul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    exact inv_mul_le_one_of_le₀ hN_ge (Nat.cast_nonneg N)
  have hreg' := (mmwu_regret hn 1 zero_lt_one le_rfl (N + 1)
    (fun t => if t ≤ N then M t else 0)
    (fun t ht => by
      rw [Finset.mem_Icc] at ht
      by_cases hle : t ≤ N
      · simp only [hle, if_true]; exact hMherm t (Finset.mem_Icc.mpr ⟨ht.1, hle⟩)
      · simp [hle])
    (fun t ht => by
      rw [Finset.mem_Icc] at ht
      by_cases hle : t ≤ N
      · simp only [hle, if_true]; exact hMnorm t (Finset.mem_Icc.mpr ⟨ht.1, hle⟩)
      · simp [hle, specNorm_zero])).1 (N + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have heq : mmwuIterate 1 (fun t => if t ≤ N then M t else 0) (N + 1) = gibbsState H := by
    unfold mmwuIterate
    congr 1
    have hsum : (∑ τ ∈ Finset.Ico 1 (N + 1), (if τ ≤ N then M τ else 0)) =
        ∑ τ ∈ Finset.Ico 1 (N + 1), M τ := by
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [Finset.mem_Ico] at hτ
      simp [show τ ≤ N by omega]
    rw [hsum]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    ext i j
    simp only [M, Matrix.smul_apply, Matrix.sum_apply]
    simp only [Finset.sum_const, Nat.card_Ico, add_tsub_cancel_right, nsmul_eq_mul, smul_eq_mul]
    push_cast
    field_simp [hN0]
  rwa [heq] at hreg'

theorem trace_eq_sum_orthonormalBasis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (B : Matrix (Fin n) (Fin n) ℂ) :
    B.trace = ∑ i : Fin n, inner ℂ (b i) (act B (b i)) := by
  have horth : ∀ j k : Fin n,
      (∑ i : Fin n, b i k * conj (b i j)) = if j = k then 1 else 0 := by
    intro j k
    set ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1 : ℂ)
    set ek : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k (1 : ℂ)
    have hrepr : ∀ (l : Fin n) (i : Fin n),
        b.repr (EuclideanSpace.single l (1 : ℂ)) i = conj (b i l) := by
      intro l i
      rw [OrthonormalBasis.repr_apply_apply, PiLp.inner_apply]
      rw [Finset.sum_eq_single l]
      · simp [RCLike.inner_apply]
      · intro m _ hm; simp [hm]
      · intro h; exact absurd (Finset.mem_univ l) h
    have h1 := b.repr.inner_map_map ek ej
    rw [PiLp.inner_apply] at h1
    have h1' : (∑ i : Fin n, b i k * conj (b i j)) = inner ℂ ek ej := by
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ek, ej, hrepr, RCLike.inner_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
      ring
    rw [h1', PiLp.inner_apply, Finset.sum_eq_single j]
    · by_cases hjk : j = k <;> simp [ej, ek, RCLike.inner_apply, hjk]
    · intro m _ hm; simp [ej, hm]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hexpand : (∑ i : Fin n, inner ℂ (b i) (act B (b i))) =
      ∑ j : Fin n, ∑ k : Fin n, B j k * (∑ i : Fin n, b i k * conj (b i j)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, act, Matrix.mulVec, dotProduct,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexpand]
  simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

theorem trace_mul_hermitian_eq_sum {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρH : ρ.IsHermitian) (B : Matrix (Fin n) (Fin n) ℂ) :
    (B * ρ).trace.re =
      ∑ i : Fin n, hρH.eigenvalues i *
        (inner ℂ (hρH.eigenvectorBasis i) (act B (hρH.eigenvectorBasis i))).re := by
  set b := hρH.eigenvectorBasis with hbdef
  set p := hρH.eigenvalues with hpdef
  have hbρ : ∀ i, act ρ (b i) = (p i : ℂ) • b i := by
    intro i
    change WithLp.toLp 2 (ρ.mulVec (b i)) = _
    rw [hbdef, hρH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hpdef]
  rw [trace_eq_sum_orthonormalBasis b (B * ρ), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [red_act_mul, hbρ i, red_act_smul_vec, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem density_eigenvalues_sum_one {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : IsDensityMatrix ρ) :
    (∑ i : Fin n, hρ.1.1.eigenvalues i) = 1 := by
  have hρH : ρ.IsHermitian := hρ.1.1
  have h1 := trace_mul_hermitian_eq_sum hρH 1
  rw [one_mul, hρ.2, Complex.one_re] at h1
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h1.symm
  rw [red_act_one, inner_self_eq_norm_sq_to_K, hρH.eigenvectorBasis.orthonormal.1 i]
  simp

theorem minEigenvalue_le_trace_mul_density {n : ℕ} (hn : 0 < n)
    {S ρ : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (hρ : IsDensityMatrix ρ) :
    minEigenvalue S ≤ (S * ρ).trace.re := by
  have h0 : 0 < Fintype.card (Fin n) := by simpa using hn
  rw [trace_mul_hermitian_eq_sum hρ.1.1 S]
  set b := hρ.1.1.eigenvectorBasis
  set p := hρ.1.1.eigenvalues
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => hρ.1.eigenvalues_nonneg i
  have hterm : ∀ i : Fin n, minEigenvalue S ≤ (inner ℂ (b i) (act S (b i))).re := by
    intro i
    have h := minEigenvalue_le_re_inner_norm_sq hS h0 (b i)
    rw [b.orthonormal.1 i, one_pow, mul_one] at h
    exact h
  calc minEigenvalue S
      = (∑ i : Fin n, p i) * minEigenvalue S := by
        rw [density_eigenvalues_sum_one hρ, one_mul]
    _ = ∑ i : Fin n, p i * minEigenvalue S := Finset.sum_mul _ _ _
    _ ≤ ∑ i : Fin n, p i * (inner ℂ (b i) (act S (b i))).re :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hp_nonneg i)

theorem trace_mul_density_le_specNorm {n : ℕ} (hn : 0 < n)
    {M ρ : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hρ : IsDensityMatrix ρ) :
    (M * ρ).trace.re ≤ specNorm M := by
  have h0 : 0 < Fintype.card (Fin n) := by simpa using hn
  have hMneg : (-M).IsHermitian := hM.neg
  have h1 := minEigenvalue_le_trace_mul_density hn hMneg hρ
  have h2 := neg_specNorm_le_minEigenvalue hMneg h0
  rw [specNorm_neg] at h2
  have h3 : (-M * ρ).trace.re = -(M * ρ).trace.re := by
    rw [neg_mul, Matrix.trace_neg, Complex.neg_re]
  linarith

theorem trace_sq_mul_density_le_one {n : ℕ} {M ρ : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hMnorm : specNorm M ≤ 1) (hρ : IsDensityMatrix ρ) :
    (M ^ 2 * ρ).trace.re ≤ 1 := by
  rw [trace_mul_hermitian_eq_sum hρ.1.1 (M ^ 2)]
  set b := hρ.1.1.eigenvectorBasis
  set p := hρ.1.1.eigenvalues
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => hρ.1.eigenvalues_nonneg i
  have hsymM : (Matrix.toEuclideanLin M).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have hM2 : ∀ i, (inner ℂ (b i) (act (M ^ 2) (b i))).re ≤ 1 := by
    intro i
    have hsq : M ^ 2 = M * M := sq M
    have hact : act M (b i) = Matrix.toEuclideanLin M (b i) := rfl
    have hinner : inner ℂ (b i) (act (M ^ 2) (b i)) = inner ℂ (act M (b i)) (act M (b i)) := by
      rw [hsq, red_act_mul, hact]
      exact (hsymM (b i) (act M (b i))).symm
    have hnorm : ‖act M (b i)‖ ≤ 1 := by
      calc ‖act M (b i)‖ ≤ specNorm M * ‖b i‖ :=
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).le_opNorm (b i)
        _ ≤ 1 * 1 := mul_le_mul hMnorm (le_of_eq (b.orthonormal.1 i)) (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    have hsq_le : ‖act M (b i)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (act M (b i))]
    have hre : (inner ℂ (act M (b i)) (act M (b i))).re = ‖act M (b i)‖ ^ 2 := by
      have h := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (act M (b i)))
      simpa [sq, Complex.mul_re] using h
    rw [hinner, hre]
    exact hsq_le
  calc (∑ i : Fin n, p i * (inner ℂ (b i) (act (M ^ 2) (b i))).re)
      ≤ ∑ i : Fin n, p i * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM2 i) (hp_nonneg i)
    _ = ∑ i : Fin n, p i := by simp
    _ = 1 := density_eigenvalues_sum_one hρ

theorem pureDensity_isHermitian {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    (pureDensity u).IsHermitian := by
  ext j k
  simp [pureDensity, mul_comm]

theorem trace_mul_pureDensity {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    (B * pureDensity u).trace = inner ℂ u (act B u) := by
  unfold pureDensity
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
    PiLp.inner_apply, RCLike.inner_apply, act, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sum_abs_diag_pureDensity {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    (∑ j : Fin n, |((pureDensity u) j j).re|) = 1 := by
  have hdiag : ∀ j : Fin n, |((pureDensity u) j j).re| = ‖u j‖ ^ 2 := by
    intro j
    have h1 : (pureDensity u) j j = ((‖u j‖ ^ 2 : ℝ) : ℂ) := by
      simp only [pureDensity, Matrix.of_apply]
      simpa [sq] using Complex.mul_conj' (u j)
    rw [h1, Complex.ofReal_re, abs_of_nonneg (sq_nonneg _)]
  simp only [hdiag]
  have hsq := EuclideanSpace.norm_sq_eq u
  rw [hu, one_pow] at hsq
  exact hsq.symm

theorem abs_trace_cHat_mul_pureDensity_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    |(cHat A * pureDensity u).trace.re| ≤ 1 := by
  rw [trace_mul_pureDensity]
  calc |(inner ℂ u (act (cHat A) u)).re|
      ≤ ‖inner ℂ u (act (cHat A) u)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖u‖ * ‖act (cHat A) u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (specNorm (cHat A) * ‖u‖) :=
        mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cHat A)).le_opNorm u)
          (norm_nonneg u)
    _ ≤ 1 * (1 * 1) := by
        rw [hu]
        gcongr
        exact specNorm_cHat_le_one A
    _ = 1 := by ring

theorem maxCutF_add_smul_pureDensity_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) :
    maxCutF A γ (X + s • pureDensity u) ≤ maxCutF A γ X + |s| := by
  unfold maxCutF
  refine max_le ?_ ?_
  · have htr : (cHat A * (X + s • pureDensity u)).trace.re =
        (cHat A * X).trace.re + s * (cHat A * pureDensity u).trace.re := by
      have hsmul : s • pureDensity u = (s : ℂ) • pureDensity u := by
        ext i j; simp [Complex.real_smul]
      rw [hsmul, mul_add, Algebra.mul_smul_comm, Matrix.trace_add, Matrix.trace_smul]
      simp [Complex.mul_re]
    have habs : -(s * (cHat A * pureDensity u).trace.re) ≤ |s| := by
      calc -(s * (cHat A * pureDensity u).trace.re)
          ≤ |s * (cHat A * pureDensity u).trace.re| := neg_le_abs _
        _ = |s| * |(cHat A * pureDensity u).trace.re| := abs_mul _ _
        _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left
            (abs_trace_cHat_mul_pureDensity_le_one A hu) (abs_nonneg s)
        _ = |s| := mul_one _
    have hle1 : γ - (cHat A * X).trace.re ≤
        max (γ - (cHat A * X).trace.re) (∑ j, |(X j j).re - (n : ℝ)⁻¹|) := le_max_left _ _
    linarith
  · have hterm : ∀ j : Fin n,
        |((X + s • pureDensity u) j j).re - (n : ℝ)⁻¹| ≤
          |(X j j).re - (n : ℝ)⁻¹| + |s| * |((pureDensity u) j j).re| := by
      intro j
      have h1 : ((X + s • pureDensity u) j j).re - (n : ℝ)⁻¹ =
          ((X j j).re - (n : ℝ)⁻¹) + s * ((pureDensity u) j j).re := by
        simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Complex.mul_re]
        ring
      rw [h1]
      exact (abs_add_le _ _).trans (by rw [abs_mul])
    calc (∑ j : Fin n, |((X + s • pureDensity u) j j).re - (n : ℝ)⁻¹|)
        ≤ ∑ j : Fin n, (|(X j j).re - (n : ℝ)⁻¹| + |s| * |((pureDensity u) j j).re|) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j : Fin n, |(X j j).re - (n : ℝ)⁻¹|) +
            |s| * (∑ j : Fin n, |((pureDensity u) j j).re|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ j : Fin n, |(X j j).re - (n : ℝ)⁻¹|) + |s| := by
          rw [sum_abs_diag_pureDensity hu, mul_one]
      _ ≤ max (γ - (cHat A * X).trace.re) (∑ j, |(X j j).re - (n : ℝ)⁻¹|) + |s| := by
          gcongr
          exact le_max_right _ _

theorem specNorm_le_one_of_isEpsSubgradOn_maxCutF {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (γ δ : ℝ)
    {ρ H : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hsub : IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
      (maxCutF A γ) δ ρ (traceRePairing H)) :
    specNorm H ≤ 1 := by
  set b := hH.eigenvectorBasis with hbdef
  set lam := hH.eigenvalues with hlamdef
  have hact_b : ∀ i : Fin n, act H (b i) = (lam i : ℂ) • b i := by
    intro i
    change WithLp.toLp 2 (H.mulVec (b i)) = _
    rw [hbdef, hH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hlamdef]
  have hlam_sq_le_one : ∀ i : Fin n, (lam i) ^ 2 ≤ 1 := by
    intro i
    have hu : ‖b i‖ = 1 := b.orthonormal.1 i
    set P := pureDensity (b i)
    have hPherm : P.IsHermitian := pureDensity_isHermitian (b i)
    have hpairP : traceRePairing H P = lam i := by
      change (H * P.conjTranspose).trace.re = lam i
      rw [hPherm.eq, trace_mul_pureDensity, hact_b i, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hu]
      simp
    have hineq : ∀ s : ℝ, s * lam i ≤ |s| + δ := by
      intro s
      have hXherm : (ρ + s • P).IsHermitian := by
        have hsmul : s • P = (s : ℂ) • P := by ext j k; simp [Complex.real_smul]
        rw [hsmul, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
          hρ.eq, hPherm.eq]
        simp
      have h1 := hsub (ρ + s • P) hXherm
      rw [add_sub_cancel_left, map_smul, smul_eq_mul, hpairP] at h1
      have h2 := maxCutF_add_smul_pureDensity_le A γ ρ s hu
      linarith
    have hle1 : lam i ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < lam i := lt_of_not_ge hgt
      set s : ℝ := (|δ| + 1) / (lam i - 1)
      have hs_pos : 0 < s := div_pos (by positivity) (by linarith)
      have h := hineq s
      rw [abs_of_pos hs_pos] at h
      have hmul : s * (lam i - 1) = |δ| + 1 := div_mul_cancel₀ (|δ| + 1) (by linarith)
      have hδ : δ ≤ |δ| := le_abs_self δ
      linarith
    have hge1 : -1 ≤ lam i := by
      by_contra hlt
      have hlt' : lam i < -1 := lt_of_not_ge hlt
      set s : ℝ := -((|δ| + 1) / (-1 - lam i))
      have hs_neg : s < 0 := neg_neg_of_pos (div_pos (by positivity) (by linarith))
      have h := hineq s
      rw [abs_of_neg hs_neg] at h
      have hmul : (-s) * (-1 - lam i) = |δ| + 1 := by
        dsimp [s]
        rw [neg_neg]
        exact div_mul_cancel₀ (|δ| + 1) (by linarith)
      have hδ : δ ≤ |δ| := le_abs_self δ
      linarith
    nlinarith
  have hsymH : (Matrix.toEuclideanLin H).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) H‖ ≤ 1
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  change ‖act H x‖ ≤ ‖x‖
  have hrepr_act : ∀ i : Fin n,
      ‖b.repr (act H x) i‖ ^ 2 = (lam i) ^ 2 * ‖b.repr x i‖ ^ 2 := by
    intro i
    have h1 : b.repr (act H x) i = (lam i : ℂ) * b.repr x i := by
      rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
      have h2 : inner ℂ (b i) (act H x) = inner ℂ (act H (b i)) x :=
        (hsymH (b i) x).symm
      rw [h2, hact_b i, inner_smul_left]
      simp
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hsq_le : ‖act H x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← b.repr.norm_map (act H x), ← b.repr.norm_map x,
      EuclideanSpace.norm_sq_eq (b.repr (act H x)), EuclideanSpace.norm_sq_eq (b.repr x)]
    calc (∑ i : Fin n, ‖b.repr (act H x) i‖ ^ 2)
        = ∑ i : Fin n, (lam i) ^ 2 * ‖b.repr x i‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => hrepr_act i
      _ ≤ ∑ i : Fin n, 1 * ‖b.repr x i‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlam_sq_le_one i) (sq_nonneg _)
      _ = ∑ i : Fin n, ‖b.repr x i‖ ^ 2 := by simp
  nlinarith [norm_nonneg (act H x), norm_nonneg x]

noncomputable def exactMaxCutSubgrad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if (∑ j : Fin n, |(ρ j j).re - (n : ℝ)⁻¹|) ≤ γ - (cHat A * ρ).trace.re then
    -cHat A
  else
    Matrix.diagonal fun j : Fin n => if (n : ℝ)⁻¹ ≤ (ρ j j).re then (1 : ℂ) else (-1 : ℂ)

theorem exactMaxCutSubgrad_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (γ : ℝ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (exactMaxCutSubgrad A γ ρ).IsHermitian := by
  unfold exactMaxCutSubgrad
  split_ifs
  · unfold cHat
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, hA.eq]
    simp
  · rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    ext j
    simp only [Pi.star_apply]
    split_ifs <;> simp

theorem exactMaxCutSubgrad_isEpsSubgradOn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.IsHermitian) (δ : ℝ) (hδ : 0 ≤ δ) :
    IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
      (maxCutF A γ) δ ρ (traceRePairing (exactMaxCutSubgrad A γ ρ)) := by
  intro X hX
  have hY : (X - ρ).IsHermitian := hX.sub hρ
  unfold exactMaxCutSubgrad
  split_ifs with hle
  · have hmax : maxCutF A γ ρ = γ - (cHat A * ρ).trace.re :=
      max_eq_left hle
    have hpair : traceRePairing (-cHat A) (X - ρ) =
        (cHat A * ρ).trace.re - (cHat A * X).trace.re := by
      change (-cHat A * (X - ρ).conjTranspose).trace.re = _
      rw [hY.eq, neg_mul, mul_sub, Matrix.trace_neg, Matrix.trace_sub,
        Complex.neg_re, Complex.sub_re]
      ring
    have hle_X : γ - (cHat A * X).trace.re ≤ maxCutF A γ X := le_max_left _ _
    linarith
  · have hle' : γ - (cHat A * ρ).trace.re ≤ ∑ j : Fin n, |(ρ j j).re - (n : ℝ)⁻¹| :=
      le_of_not_ge hle
    have hmax : maxCutF A γ ρ = ∑ j : Fin n, |(ρ j j).re - (n : ℝ)⁻¹| :=
      max_eq_right hle'
    set d : Fin n → ℂ := fun j => if (n : ℝ)⁻¹ ≤ (ρ j j).re then (1 : ℂ) else (-1 : ℂ)
    have hpair : traceRePairing (Matrix.diagonal d) (X - ρ) =
        ∑ j : Fin n, (if (n : ℝ)⁻¹ ≤ (ρ j j).re then (1 : ℝ) else (-1 : ℝ)) *
          ((X j j).re - (ρ j j).re) := by
      change (Matrix.diagonal d * (X - ρ).conjTranspose).trace.re = _
      rw [hY.eq, Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.diag, Matrix.diagonal_mul, Matrix.sub_apply, d]
      split_ifs <;> simp [Complex.sub_re]
    have hterm : ∀ j : Fin n,
        |(ρ j j).re - (n : ℝ)⁻¹| +
          (if (n : ℝ)⁻¹ ≤ (ρ j j).re then (1 : ℝ) else (-1 : ℝ)) * ((X j j).re - (ρ j j).re) ≤
          |(X j j).re - (n : ℝ)⁻¹| := by
      intro j
      split_ifs with hj
      · rw [abs_of_nonneg (by linarith)]
        linarith [le_abs_self ((X j j).re - (n : ℝ)⁻¹)]
      · rw [abs_of_neg (by linarith)]
        linarith [neg_le_abs ((X j j).re - (n : ℝ)⁻¹)]
    have hsum : (∑ j : Fin n, |(ρ j j).re - (n : ℝ)⁻¹|) +
        traceRePairing (Matrix.diagonal d) (X - ρ) ≤
        ∑ j : Fin n, |(X j j).re - (n : ℝ)⁻¹| := by
      rw [hpair, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => hterm j
    have hle_X : (∑ j : Fin n, |(X j j).re - (n : ℝ)⁻¹|) ≤ maxCutF A γ X := le_max_right _ _
    linarith

theorem maxCutF_average_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    (T : ℕ) (hT : 0 < T) (ρ : ℕ → Matrix (Fin n) (Fin n) ℂ) :
    maxCutF A γ (((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, ρ t) ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, maxCutF A γ (ρ t) := by
  have hTR_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hTR0 : (T : ℝ) ≠ 0 := hTR_pos.ne'
  unfold maxCutF
  refine max_le ?_ ?_
  · have htr : (cHat A * (((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, ρ t)).trace.re =
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, (cHat A * ρ t).trace.re := by
      rw [Algebra.mul_smul_comm, Finset.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
      simp [Complex.mul_re, Complex.re_sum]
    have hγ_eq : γ - (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, (cHat A * ρ t).trace.re =
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, (γ - (cHat A * ρ t).trace.re) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
        nsmul_eq_mul, mul_sub, inv_mul_cancel_left₀ hTR0]
    rw [htr, hγ_eq]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => le_max_left _ _) (inv_nonneg.mpr hTR_pos.le)
  · have hdiag : ∀ j : Fin n,
        |((((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, ρ t) j j).re - (n : ℝ)⁻¹| ≤
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, |(ρ t j j).re - (n : ℝ)⁻¹| := by
      intro j
      have h1 : ((((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, ρ t) j j).re - (n : ℝ)⁻¹ =
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, ((ρ t j j).re - (n : ℝ)⁻¹) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
          nsmul_eq_mul, mul_sub, inv_mul_cancel_left₀ hTR0]
        simp [Matrix.smul_apply, Matrix.sum_apply, Complex.mul_re, Complex.re_sum]
      rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hTR_pos)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hTR_pos.le)
    calc (∑ j : Fin n, |((((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, ρ t) j j).re - (n : ℝ)⁻¹|)
        ≤ ∑ j : Fin n, (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, |(ρ t j j).re - (n : ℝ)⁻¹| :=
          Finset.sum_le_sum fun j _ => hdiag j
      _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, ∑ j : Fin n, |(ρ t j j).re - (n : ℝ)⁻¹| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
            max (γ - (cHat A * ρ t).trace.re) (∑ j, |(ρ t j j).re - (n : ℝ)⁻¹|) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => le_max_right _ _)
            (inv_nonneg.mpr hTR_pos.le)

end MirrorDescentMaxCutAux

open MirrorDescentMaxCutAux

theorem solution {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (_hC0 : C ≠ 0) (γ : ℝ) (_hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∃ ρs : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix ρs ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρs = 0)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ t, 1 ≤ t → t < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      (G t).IsHermitian ∧
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) (mmwuIterate (ε * 16⁻¹) G t)
          (traceRePairing (G t))) :
    (∀ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊,
        IsDensityMatrix (mmwuIterate (ε * 16⁻¹) G t)) ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ
        (((⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ : ℕ) : ℂ)⁻¹ •
          ∑ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊, mmwuIterate (ε * 16⁻¹) G t) ≤ ε := by
  have hn0 : 0 < n := by omega
  set A := C.map ((↑) : ℝ → ℂ)
  have hAherm : A.IsHermitian := by
    ext i j
    simp only [A, Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]
    exact congrArg ((↑) : ℝ → ℂ) (hC.apply i j)
  set T : ℕ := ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ with hTdef
  set η : ℝ := ε * 16⁻¹ with hηdef
  have hη_pos : 0 < η := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_one : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogb_pos : 0 < Real.logb 2 n := div_pos hlogn_pos hlog2_pos
  have hlog_le_logb : Real.log n ≤ Real.logb 2 n := by
    unfold Real.logb
    exact le_div_self hlogn_pos.le hlog2_pos hlog2_le_one
  have hT_arg_pos : 0 < 64 * (ε ^ 2)⁻¹ * Real.logb 2 n := by positivity
  have hT_pos : 0 < T := Nat.ceil_pos.mpr hT_arg_pos
  have hTR_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT_pos
  have hT_ge : 64 * (ε ^ 2)⁻¹ * Real.log n ≤ T := by
    calc 64 * (ε ^ 2)⁻¹ * Real.log n
        ≤ 64 * (ε ^ 2)⁻¹ * Real.logb 2 n :=
          mul_le_mul_of_nonneg_left hlog_le_logb (by positivity)
      _ ≤ T := Nat.le_ceil _
  have hdens : ∀ t ∈ Finset.Icc 1 T, IsDensityMatrix (mmwuIterate η G t) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    apply gibbsState_isDensityMatrix hn0
    have hsum : (∑ τ ∈ Finset.Ico 1 t, G τ).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [Finset.mem_Ico] at hτ
      exact (hG τ hτ.1 (lt_of_lt_of_le hτ.2 ht.2)).1.eq
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hsum.eq]
    simp
  refine ⟨hdens, ?_⟩
  obtain ⟨ρs, hρs_dens, hρs_zero⟩ := hfeas
  set G_T := exactMaxCutSubgrad A γ (mmwuIterate η G T)
  set G' : ℕ → Matrix (Fin n) (Fin n) ℂ := fun t => if t < T then G t else G_T
  have hiter_eq : ∀ t ∈ Finset.Icc 1 T, mmwuIterate η G' t = mmwuIterate η G t := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    unfold mmwuIterate
    congr 2
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Finset.mem_Ico] at hτ
    simp [G', show τ < T by omega]
  have hG'_herm : ∀ t ∈ Finset.Icc 1 T, (G' t).IsHermitian := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases hlt : t < T
    · simp only [G', hlt, if_true]
      exact (hG t ht.1 hlt).1
    · simp only [G', hlt, if_false]
      exact exactMaxCutSubgrad_isHermitian hAherm γ (mmwuIterate η G T)
  have hG'_sub : ∀ t ∈ Finset.Icc 1 T,
      IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
        (maxCutF A γ) (ε * 2⁻¹) (mmwuIterate η G t) (traceRePairing (G' t)) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases hlt : t < T
    · simp only [G', hlt, if_true]
      exact (hG t ht.1 hlt).2
    · have ht_eq : t = T := by omega
      subst ht_eq
      simp only [G', lt_irrefl, if_false]
      exact exactMaxCutSubgrad_isEpsSubgradOn A γ
        (hdens T (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).1.1 (ε * 2⁻¹) (by positivity)
  have hG'_norm : ∀ t ∈ Finset.Icc 1 T, specNorm (G' t) ≤ 1 := by
    intro t ht
    exact specNorm_le_one_of_isEpsSubgradOn_maxCutF A γ (ε * 2⁻¹)
      (hdens t ht).1.1 (hG'_herm t ht) (hG'_sub t ht)
  have hstep_bound : ∀ t ∈ Finset.Icc 1 T,
      maxCutF A γ (mmwuIterate η G t) ≤
        (G' t * mmwuIterate η G t).trace.re - (G' t * ρs).trace.re + ε * 2⁻¹ := by
    intro t ht
    have hsub := hG'_sub t ht ρs hρs_dens.1.1
    rw [hρs_zero] at hsub
    have hdiff_herm : (ρs - mmwuIterate η G t).IsHermitian :=
      hρs_dens.1.1.sub (hdens t ht).1.1
    have hpair : traceRePairing (G' t) (ρs - mmwuIterate η G t) =
        (G' t * ρs).trace.re - (G' t * mmwuIterate η G t).trace.re := by
      change (G' t * (ρs - mmwuIterate η G t).conjTranspose).trace.re = _
      rw [hdiff_herm.eq, mul_sub, Matrix.trace_sub, Complex.sub_re]
    linarith
  have havg_le := maxCutF_average_le A γ T hT_pos (mmwuIterate η G)
  rcases le_or_gt ε 16 with hε_le | hε_gt
  · have hη_le_one : η ≤ 1 := by linarith
    set S := ∑ t ∈ Finset.Icc 1 T, G' t
    obtain ⟨_, hreg⟩ := mmwu_regret hn0 η hη_pos hη_le_one T G' hG'_herm hG'_norm
    have hreg_iter : (∑ t ∈ Finset.Icc 1 T, G' t * mmwuIterate η G t).trace.re ≤
        minEigenvalue S +
          η * (∑ t ∈ Finset.Icc 1 T, G' t ^ 2 * mmwuIterate η G t).trace.re +
          Real.log n / η := by
      have heq1 : (∑ t ∈ Finset.Icc 1 T, G' t * mmwuIterate η G t) =
          ∑ t ∈ Finset.Icc 1 T, G' t * mmwuIterate η G' t :=
        Finset.sum_congr rfl fun t ht => by rw [hiter_eq t ht]
      have heq2 : (∑ t ∈ Finset.Icc 1 T, G' t ^ 2 * mmwuIterate η G t) =
          ∑ t ∈ Finset.Icc 1 T, G' t ^ 2 * mmwuIterate η G' t :=
        Finset.sum_congr rfl fun t ht => by rw [hiter_eq t ht]
      rw [heq1, heq2]
      exact hreg
    have hSherm : S.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun t ht => (hG'_herm t ht).eq
    have hminS_le : minEigenvalue S ≤ (S * ρs).trace.re :=
      minEigenvalue_le_trace_mul_density hn0 hSherm hρs_dens
    have hsq_sum_le : (∑ t ∈ Finset.Icc 1 T, G' t ^ 2 * mmwuIterate η G t).trace.re ≤ T := by
      rw [Matrix.trace_sum, Complex.re_sum]
      calc (∑ t ∈ Finset.Icc 1 T, (G' t ^ 2 * mmwuIterate η G t).trace.re)
          ≤ ∑ _t ∈ Finset.Icc 1 T, (1 : ℝ) :=
            Finset.sum_le_sum fun t ht =>
              trace_sq_mul_density_le_one (hG'_herm t ht) (hG'_norm t ht) (hdens t ht)
        _ = T := by simp [Finset.sum_const, Nat.card_Icc]
    have hsum_step : (∑ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t)) ≤
        (∑ t ∈ Finset.Icc 1 T, G' t * mmwuIterate η G t).trace.re -
          (S * ρs).trace.re + (T : ℝ) * (ε * 2⁻¹) := by
      calc (∑ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t))
          ≤ ∑ t ∈ Finset.Icc 1 T,
              ((G' t * mmwuIterate η G t).trace.re - (G' t * ρs).trace.re + ε * 2⁻¹) :=
            Finset.sum_le_sum hstep_bound
        _ = (∑ t ∈ Finset.Icc 1 T, (G' t * mmwuIterate η G t).trace.re) -
              (∑ t ∈ Finset.Icc 1 T, (G' t * ρs).trace.re) +
              ∑ _t ∈ Finset.Icc 1 T, (ε * 2⁻¹) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (∑ t ∈ Finset.Icc 1 T, G' t * mmwuIterate η G t).trace.re -
              (S * ρs).trace.re + (T : ℝ) * (ε * 2⁻¹) := by
            rw [← Complex.re_sum, ← Matrix.trace_sum, ← Complex.re_sum, ← Matrix.trace_sum,
              ← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
              nsmul_eq_mul]
    have hlog_bound : Real.log n / η ≤ (T : ℝ) * (ε * 4⁻¹) := by
      rw [div_le_iff₀ hη_pos]
      calc Real.log n
          = (64 * (ε ^ 2)⁻¹ * Real.log n) * (ε ^ 2 / 64) := by
            field_simp [hε.ne']
        _ ≤ (T : ℝ) * (ε ^ 2 / 64) :=
            mul_le_mul_of_nonneg_right hT_ge (by positivity)
        _ = (T : ℝ) * (ε * 4⁻¹) * η := by
            rw [hηdef]; ring
    have hsum_ub : (∑ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t)) ≤ (T : ℝ) * ε := by
      have h1 : η * (∑ t ∈ Finset.Icc 1 T, G' t ^ 2 * mmwuIterate η G t).trace.re ≤
          (T : ℝ) * (ε * 16⁻¹) := by
        rw [← hηdef, mul_comm (T : ℝ) η]
        exact mul_le_mul_of_nonneg_left hsq_sum_le hη_pos.le
      have hTε : 0 < (T : ℝ) * ε := mul_pos hTR_pos hε
      linarith
    calc maxCutF A γ (((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, mmwuIterate η G t)
        ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t) := havg_le
      _ ≤ (T : ℝ)⁻¹ * ((T : ℝ) * ε) :=
          mul_le_mul_of_nonneg_left hsum_ub (inv_nonneg.mpr hTR_pos.le)
      _ = ε := inv_mul_cancel_left₀ hTR_pos.ne' ε
  · have hterm_ub : ∀ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t) ≤ ε := by
      intro t ht
      have h1 : (G' t * mmwuIterate η G t).trace.re ≤ 1 :=
        (trace_mul_density_le_specNorm hn0 (hG'_herm t ht) (hdens t ht)).trans (hG'_norm t ht)
      have h2 : -(G' t * ρs).trace.re ≤ 1 := by
        have h := trace_mul_density_le_specNorm hn0 (hG'_herm t ht).neg hρs_dens
        rw [neg_mul, Matrix.trace_neg, Complex.neg_re, specNorm_neg] at h
        exact h.trans (hG'_norm t ht)
      have h3 := hstep_bound t ht
      linarith
    calc maxCutF A γ (((T : ℕ) : ℂ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, mmwuIterate η G t)
        ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, maxCutF A γ (mmwuIterate η G t) := havg_le
      _ ≤ (T : ℝ)⁻¹ * ∑ _t ∈ Finset.Icc 1 T, ε :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm_ub) (inv_nonneg.mpr hTR_pos.le)
      _ = ε := by
          rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
            inv_mul_cancel_left₀ hTR_pos.ne']
