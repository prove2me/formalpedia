-- Prove2me | solution 1 for QAlgorithms.Nannicini.mmwuSDP_correct
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:24:38.803412+00:00
-- url     : https://prove2.me/submissions/fc6fdc4f-0e08-4a3c-899a-5f7600211db4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Defs_SDP
import Theorems.Thm_QAlgorithms_Nannicini_mmwu_regret
import Theorems.Thm_QAlgorithms_Nannicini_picPolytope_certificate

set_option autoImplicit false

open QAlgorithms QAlgorithms.SDP QAlgorithms.Nannicini
open scoped ComplexOrder ComplexConjugate

namespace MMWUSDPAux

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

theorem posSemidef_smul_add_one {n : ℕ} (hn : 0 < n) {S : Matrix (Fin n) (Fin n) ℂ}
    (hS : S.IsHermitian) (a c : ℝ) (ha : 0 ≤ a) (hmin : 0 ≤ a * minEigenvalue S + c) :
    (((a : ℝ) : ℂ) • S + ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have h0 : 0 < Fintype.card (Fin n) := by simpa using hn
  have hHerm : (((a : ℝ) : ℂ) • S + ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hS.eq]
    simp
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHerm, fun v => ?_⟩
  set x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hdot : dotProduct (star v)
      ((((a : ℝ) : ℂ) • S + ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec v) =
      ((a * (inner ℂ x (act S x)).re + c * ‖x‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : dotProduct (star v)
        ((((a : ℝ) : ℂ) • S + ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec v) =
        inner ℂ x (act (((a : ℝ) : ℂ) • S + ((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) x) := by
      simp [x, PiLp.inner_apply, act, dotProduct, mul_comm]
    rw [h1, red_act_add, red_act_smul, red_act_smul, red_act_one,
      inner_add_right, inner_smul_right, inner_smul_right, inner_act_eq_sum hS x,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_re]
    push_cast
    rfl
  rw [hdot]
  have hSx := minEigenvalue_le_re_inner_norm_sq hS h0 x
  have h1 : a * (minEigenvalue S * ‖x‖ ^ 2) ≤ a * (inner ℂ x (act S x)).re :=
    mul_le_mul_of_nonneg_left hSx ha
  have h2 : 0 ≤ (a * minEigenvalue S + c) * ‖x‖ ^ 2 :=
    mul_nonneg hmin (sq_nonneg _)
  have h3 : 0 ≤ a * (inner ℂ x (act S x)).re + c * ‖x‖ ^ 2 := by linarith
  exact_mod_cast h3

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

theorem specNorm_sum_le {ι α : Type*} [Fintype ι] [DecidableEq ι] (s : Finset α)
    (f : α → Matrix ι ι ℂ) :
    specNorm (∑ a ∈ s, f a) ≤ ∑ a ∈ s, specNorm (f a) := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (∑ a ∈ s, f a)‖ ≤
    ∑ a ∈ s, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (f a)‖
  rw [map_sum]
  exact norm_sum_le s _

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

theorem trace_sq_mul_density_le_one {n : ℕ} {M ρ : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) (hMnorm : specNorm M ≤ 1) (hρ : IsDensityMatrix ρ) :
    (M ^ 2 * ρ).trace.re ≤ 1 := by
  have hρH : ρ.IsHermitian := hρ.1.1
  set b := hρH.eigenvectorBasis with hbdef
  set p := hρH.eigenvalues with hpdef
  have hsymρ : (Matrix.toEuclideanLin ρ).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hρH
  have hbρ : ∀ i, act ρ (b i) = (p i : ℂ) • b i := by
    intro i
    change WithLp.toLp 2 (ρ.mulVec (b i)) = _
    rw [hbdef, hρH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul, hpdef]
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => hρ.1.eigenvalues_nonneg i
  have htrace_B : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      (B * ρ).trace.re = ∑ i : Fin n, p i * (inner ℂ (b i) (act B (b i))).re := by
    intro B
    rw [trace_eq_sum_orthonormalBasis b (B * ρ), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [red_act_mul, hbρ i, red_act_smul_vec, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp_sum : (∑ i : Fin n, p i) = 1 := by
    have h1 := htrace_B 1
    rw [one_mul, hρ.2, Complex.one_re] at h1
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h1.symm
    rw [red_act_one, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [htrace_B (M ^ 2)]
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
    _ = 1 := hp_sum

theorem mmwuLoss_isHermitian {n m : ℕ} {A : Fin m → Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin n) ℂ} (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (w : ℝ) (ys : List (Fin m → ℝ)) (τ : ℕ) :
    (mmwuLoss A C w ys τ).IsHermitian := by
  unfold mmwuLoss
  have hsum : (∑ j : Fin m, ((ys.getD (τ - 1) 0 j : ℝ) : ℂ) • A j).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_smul, (hAherm j).eq]
    simp
  have hsub : (∑ j : Fin m, ((ys.getD (τ - 1) 0 j : ℝ) : ℂ) • A j - C).IsHermitian :=
    hsum.sub hCherm
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hsub.eq]
  simp

theorem mmwuIterate_isDensityMatrix {n m : ℕ} (hn : 0 < n)
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (η w : ℝ) (ys : List (Fin m → ℝ)) (t : ℕ) :
    IsDensityMatrix (mmwuIterate η (mmwuLoss A C w ys) t) := by
  apply gibbsState_isDensityMatrix hn
  have hsum : (∑ τ ∈ Finset.Ico 1 t, mmwuLoss A C w ys τ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun τ _ => (mmwuLoss_isHermitian hAherm hCherm w ys τ).eq
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hsum.eq]
  simp

theorem mmwuRun_inl_prop {n m : ℕ} (hn : 0 < n)
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (R : ℝ) (hR : 0 < R) (η w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
      mmwuRun A C R η w O k = Sum.inl X → X.PosSemidef ∧ O X = none := by
  intro k
  induction k with
  | zero =>
    intro X h
    simp [mmwuRun] at h
  | succ k ih =>
    intro X h
    simp only [mmwuRun] at h
    cases hrun : mmwuRun A C R η w O k with
    | inl X' =>
      rw [hrun] at h
      simp only [Sum.inl.injEq] at h
      subst h
      exact ih X' hrun
    | inr ys =>
      rw [hrun] at h
      dsimp only at h
      set Xnext := (R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1) with hXnext
      cases hO : O Xnext with
      | none =>
        rw [hO] at h
        simp only [Sum.inl.injEq] at h
        subst h
        refine ⟨?_, hO⟩
        have hdens := mmwuIterate_isDensityMatrix hn hAherm hCherm η w ys (k + 1)
        have hsmul : Xnext = R • mmwuIterate η (mmwuLoss A C w ys) (k + 1) := by
          ext i j; simp [Xnext, Complex.real_smul]
        rw [hsmul]
        exact hdens.1.smul hR.le
      | some y =>
        rw [hO] at h
        simp at h

theorem mmwuLoss_append {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (w : ℝ) (ys : List (Fin m → ℝ)) (y : Fin m → ℝ)
    (τ : ℕ) (hτ1 : 1 ≤ τ) (hτ : τ ≤ ys.length) :
    mmwuLoss A C w (ys ++ [y]) τ = mmwuLoss A C w ys τ := by
  unfold mmwuLoss
  have hlt : τ - 1 < ys.length := by omega
  have hget : (ys ++ [y]).getD (τ - 1) 0 = ys.getD (τ - 1) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  rw [hget]

theorem mmwuIterate_append {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (η w : ℝ) (ys : List (Fin m → ℝ)) (y : Fin m → ℝ)
    (t : ℕ) (ht : t ≤ ys.length + 1) :
    mmwuIterate η (mmwuLoss A C w (ys ++ [y])) t =
      mmwuIterate η (mmwuLoss A C w ys) t := by
  unfold mmwuIterate
  congr 2
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [Finset.mem_Ico] at hτ
  exact mmwuLoss_append A C w ys y τ hτ.1 (by omega)

theorem mmwuRun_inr_prop {n m : ℕ} (hn : 0 < n)
    {A : Fin m → Matrix (Fin n) (Fin n) ℂ} {b : Fin m → ℝ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (R : ℝ) (hR : 0 < R) (γ ε w η : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ))
    (hO : IsPICOracle A b C γ (ε / 3) w O) :
    ∀ (k : ℕ) (ys : List (Fin m → ℝ)),
      mmwuRun A C R η w O k = Sum.inr ys →
      ys.length = k ∧
      ys.sum = (∑ τ ∈ Finset.Icc 1 k, ys.getD (τ - 1) 0) ∧
      ∀ τ ∈ Finset.Icc 1 k,
        ys.getD (τ - 1) 0 ∈
          picPolytope A b C γ (ε / 3) ((R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) τ) ∧
        specNorm (∑ j, ((ys.getD (τ - 1) 0 j : ℝ) : ℂ) • A j - C) ≤ w := by
  intro k
  induction k with
  | zero =>
    intro ys h
    simp only [mmwuRun, Sum.inr.injEq] at h
    subst h
    simp
  | succ k ih =>
    intro ys' h
    simp only [mmwuRun] at h
    cases hrun : mmwuRun A C R η w O k with
    | inl X =>
      rw [hrun] at h
      simp at h
    | inr ys =>
      rw [hrun] at h
      dsimp only at h
      set Xnext := (R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1) with hXnext
      cases hO_call : O Xnext with
      | none =>
        rw [hO_call] at h
        simp at h
      | some y =>
        rw [hO_call] at h
        simp only [Sum.inr.injEq] at h
        subst h
        obtain ⟨hlen, hsum, hprop⟩ := ih ys hrun
        have hX_psd : Xnext.PosSemidef := by
          have hdens := mmwuIterate_isDensityMatrix hn hAherm hCherm η w ys (k + 1)
          have hsmul : Xnext = R • mmwuIterate η (mmwuLoss A C w ys) (k + 1) := by
            ext i j; simp [Xnext, Complex.real_smul]
          rw [hsmul]
          exact hdens.1.smul hR.le
        have hy_oracle := (hO Xnext hX_psd).2 y hO_call
        have hget_left : ∀ τ ∈ Finset.Icc 1 k, (ys ++ [y]).getD (τ - 1) 0 = ys.getD (τ - 1) 0 := by
          intro τ hτ
          rw [Finset.mem_Icc] at hτ
          have hlt : τ - 1 < ys.length := by omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        have hget_last : (ys ++ [y]).getD k 0 = y := by
          simp [List.getD_eq_getElem?_getD, ← hlen]
        refine ⟨by simp [hlen], ?_, ?_⟩
        · have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
            ext τ; simp [Finset.mem_Icc]; omega
          rw [List.sum_append, List.sum_singleton, hIcc,
            Finset.sum_insert (by simp [Finset.mem_Icc]),
            Nat.add_sub_cancel, hget_last, add_comm]
          congr 1
          rw [hsum]
          refine Finset.sum_congr rfl fun τ hτ => (hget_left τ hτ).symm
        · intro τ hτ
          rw [Finset.mem_Icc] at hτ
          rcases eq_or_lt_of_le hτ.2 with rfl | hlt
          · rw [Nat.add_sub_cancel, hget_last,
              mmwuIterate_append A C η w ys y (k + 1) (by omega)]
            exact hy_oracle
          · have hτk : τ ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hτ.1, by omega⟩
            rw [hget_left τ hτk, mmwuIterate_append A C η w ys y τ (by omega)]
            exact hprop τ hτk

end MMWUSDPAux

open MMWUSDPAux in
theorem solution {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ) (hAherm : ∀ j, (A j).IsHermitian) (hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (hb1 : b ⟨0, hm⟩ = R) (hR : 0 < R) (hC : specNorm C ≤ 1)
    (γ ε w : ℝ) (hε : 0 < ε) (hw : 0 < w)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ))
    (hO : IsPICOracle A b C γ (ε / 3) w O) :
    (∀ X : Matrix (Fin n) (Fin n) ℂ, mmwuSDP A C R ε w O = Sum.inl X →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    (∀ y : Fin m → ℝ, mmwuSDP A C R ε w O = Sum.inr y →
      DualFeasible A C y ∧ ∑ j, b j * y j ≤ γ + ε) := by
  have hn0 : 0 < n := by omega
  set T : ℕ := ⌈9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹⌉₊ with hTdef
  set η : ℝ := Real.sqrt (Real.log n * (T : ℝ)⁻¹) with hηdef
  constructor
  · intro X hSDP
    dsimp only [mmwuSDP] at hSDP
    rw [← hTdef, ← hηdef] at hSDP
    cases hrun : mmwuRun A C R η w O T with
    | inr ys =>
      rw [hrun] at hSDP
      simp at hSDP
    | inl X' =>
      rw [hrun] at hSDP
      simp only [Sum.inl.injEq] at hSDP
      subst hSDP
      obtain ⟨hX_psd, hO_none⟩ := mmwuRun_inl_prop hn0 hAherm hCherm R hR η w O T X' hrun
      have hemp : picPolytope A b C γ (ε / 3) X' = ∅ := (hO X' hX_psd).1.mp hO_none
      exact (picPolytope_certificate hm A b C R hAherm hCherm hA1 hb1 hR hC γ (ε / 3)
        (by positivity) X' hX_psd).1 hemp
  · intro ybar hSDP
    dsimp only [mmwuSDP] at hSDP
    rw [← hTdef, ← hηdef] at hSDP
    cases hrun : mmwuRun A C R η w O T with
    | inl X =>
      rw [hrun] at hSDP
      simp at hSDP
    | inr ys =>
      rw [hrun] at hSDP
      simp only [Sum.inr.injEq] at hSDP
      obtain ⟨hlen, hsum_ys, hprop⟩ :=
        mmwuRun_inr_prop hn0 hAherm hCherm R hR γ ε w η O hO T ys hrun
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hT_arg_pos : 0 < 9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹ := by positivity
      have hT_pos : 0 < T := Nat.ceil_pos.mpr hT_arg_pos
      have hTR_pos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT_pos
      have hT_ge : 9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹ ≤ T := Nat.le_ceil _
      set M : ℕ → Matrix (Fin n) (Fin n) ℂ := mmwuLoss A C w ys
      set yseq : ℕ → Fin m → ℝ := fun τ => ys.getD (τ - 1) 0
      have hybar_apply : ∀ j : Fin m,
          ybar j = (T : ℝ)⁻¹ * (∑ t ∈ Finset.Icc 1 T, yseq t j) +
            ε * R⁻¹ * (if (j : ℕ) = 0 then 1 else 0) := by
        intro j
        rw [← hSDP, hsum_ys]
        simp [yseq, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
      have hy_nonneg : ∀ j : Fin m, 0 ≤ ybar j := by
        intro j
        rw [hybar_apply j]
        refine add_nonneg (mul_nonneg (inv_nonneg.mpr hTR_pos.le)
          (Finset.sum_nonneg fun t ht => (hprop t ht).1.2.2 j)) ?_
        by_cases hj : (j : ℕ) = 0 <;> simp [hj]
        positivity
      have he0_sum : (∑ j : Fin m, b j * (if (j : ℕ) = 0 then 1 else 0)) = R := by
        rw [Finset.sum_eq_single ⟨0, hm⟩]
        · simp [hb1]
        · intro j _ hj
          have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
          simp [hj0]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hby_le : (∑ j : Fin m, b j * ybar j) ≤ γ + ε := by
        have h1 : (∑ j : Fin m, b j * ybar j) =
            (T : ℝ)⁻¹ * (∑ t ∈ Finset.Icc 1 T, ∑ j : Fin m, b j * yseq t j) +
              ε * R⁻¹ * (∑ j : Fin m, b j * (if (j : ℕ) = 0 then 1 else 0)) := by
          simp only [hybar_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ =>
              Finset.sum_congr rfl fun j _ => by ring
          · refine Finset.sum_congr rfl fun j _ => by ring
        rw [h1, he0_sum, mul_assoc, inv_mul_cancel₀ hR.ne', mul_one]
        have hsum_le : (∑ t ∈ Finset.Icc 1 T, ∑ j : Fin m, b j * yseq t j) ≤
            ∑ _t ∈ Finset.Icc 1 T, γ :=
          Finset.sum_le_sum fun t ht => (hprop t ht).1.1
        simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum_le
        have h2 : (T : ℝ)⁻¹ * (∑ t ∈ Finset.Icc 1 T, ∑ j : Fin m, b j * yseq t j) ≤ γ := by
          calc (T : ℝ)⁻¹ * (∑ t ∈ Finset.Icc 1 T, ∑ j : Fin m, b j * yseq t j)
              ≤ (T : ℝ)⁻¹ * ((T : ℝ) * γ) :=
                mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hTR_pos.le)
            _ = γ := inv_mul_cancel_left₀ hTR_pos.ne' γ
        linarith
      have hMherm : ∀ t ∈ Finset.Icc 1 T, (M t).IsHermitian :=
        fun t _ => mmwuLoss_isHermitian hAherm hCherm w ys t
      have hMnorm : ∀ t ∈ Finset.Icc 1 T, specNorm (M t) ≤ 1 := by
        intro t ht
        dsimp [M, mmwuLoss]
        rw [specNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hw.le]
        exact inv_mul_le_one_of_le₀ (hprop t ht).2 hw.le
      set S : Matrix (Fin n) (Fin n) ℂ := ∑ t ∈ Finset.Icc 1 T, M t
      have hSherm : S.IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
        exact Finset.sum_congr rfl fun t ht => (hMherm t ht).eq
      have hmat_eq : (∑ j : Fin m, (ybar j : ℂ) • A j - C) =
          (((w * (T : ℝ)⁻¹ : ℝ) : ℂ) • S + ((ε * R⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
        have he0_A : (∑ j : Fin m, (((if (j : ℕ) = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) • A j) = 1 := by
          rw [Finset.sum_eq_single ⟨0, hm⟩]
          · simp [hA1]
          · intro j _ hj
            have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
            simp [hj0]
          · intro h; exact absurd (Finset.mem_univ _) h
        have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
        have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT_pos.ne'
        have hM_term : ∀ t : ℕ,
            (∑ j : Fin m, (yseq t j : ℂ) • A j) = (w : ℂ) • M t + C := by
          intro t
          dsimp only [M, mmwuLoss, yseq]
          rw [smul_smul, mul_inv_cancel₀ hw0, one_smul, sub_add_cancel]
        have hsum_comm : (∑ j : Fin m, (((∑ t ∈ Finset.Icc 1 T, yseq t j) : ℝ) : ℂ) • A j) =
            (w : ℂ) • S + (T : ℂ) • C := by
          have h1 : (∑ j : Fin m, (((∑ t ∈ Finset.Icc 1 T, yseq t j) : ℝ) : ℂ) • A j) =
              ∑ t ∈ Finset.Icc 1 T, ∑ j : Fin m, (yseq t j : ℂ) • A j := by
            simp only [Complex.ofReal_sum, Finset.sum_smul]
            exact Finset.sum_comm
          have hsumC : (∑ _t ∈ Finset.Icc 1 T, C) = (T : ℂ) • C := by
            ext i k
            simp [Matrix.sum_apply, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          rw [h1]
          simp only [hM_term, Finset.sum_add_distrib, ← Finset.smul_sum, hsumC]
          rfl
        have hybar_sum : (∑ j : Fin m, (ybar j : ℂ) • A j) =
            ((T : ℂ)⁻¹) • ((w : ℂ) • S + (T : ℂ) • C) + ((ε * R⁻¹ : ℝ) : ℂ) • 1 := by
          have h2 : (∑ j : Fin m, (ybar j : ℂ) • A j) =
              ((T : ℂ)⁻¹) • (∑ j : Fin m, (((∑ t ∈ Finset.Icc 1 T, yseq t j) : ℝ) : ℂ) • A j) +
                ((ε * R⁻¹ : ℝ) : ℂ) • (∑ j : Fin m, (((if (j : ℕ) = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) • A j) := by
            simp only [hybar_apply, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_inv,
              Complex.ofReal_natCast, add_smul, Finset.sum_add_distrib, ← smul_smul,
              ← Finset.smul_sum]
          rw [h2, hsum_comm, he0_A]
        rw [hybar_sum, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hT0, one_smul]
        ext i k
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
        ring
      have hminS : 0 ≤ w * (T : ℝ)⁻¹ * minEigenvalue S + ε * R⁻¹ := by
        rcases le_or_gt ε (3 * w * R) with hε_le | hε_gt
        · have h1 : 1 ≤ 3 * w * R * ε⁻¹ := by
            rw [le_mul_inv_iff₀ hε]; linarith
          have hsq1 : 1 ≤ 9 * w ^ 2 * R ^ 2 * (ε ^ 2)⁻¹ := by
            have : (3 * w * R * ε⁻¹) ^ 2 = 9 * w ^ 2 * R ^ 2 * (ε ^ 2)⁻¹ := by ring
            nlinarith
          have hlog_le_T : Real.log n ≤ T := by
            calc Real.log n = 1 * Real.log n := (one_mul _).symm
              _ ≤ (9 * w ^ 2 * R ^ 2 * (ε ^ 2)⁻¹) * Real.log n :=
                  mul_le_mul_of_nonneg_right hsq1 hlogn.le
              _ = 9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹ := by ring
              _ ≤ T := hT_ge
          have hη_pos : 0 < η := Real.sqrt_pos.mpr (by positivity)
          have hη_le_one : η ≤ 1 := by
            rw [hηdef, Real.sqrt_le_one]
            exact mul_inv_le_one_of_le₀ hlog_le_T hTR_pos.le
          have hη_sq : η ^ 2 = Real.log n * (T : ℝ)⁻¹ :=
            Real.sq_sqrt (by positivity)
          obtain ⟨hdens, hreg⟩ := mmwu_regret hn0 η hη_pos hη_le_one T M hMherm hMnorm
          have hloss_lb : -(T : ℝ) * (ε / (3 * w * R)) ≤
              (∑ t ∈ Finset.Icc 1 T, M t * mmwuIterate η M t).trace.re := by
            have hterm : ∀ t ∈ Finset.Icc 1 T,
                -(ε / (3 * w * R)) ≤ (M t * mmwuIterate η M t).trace.re := by
              intro t ht
              have hpic := (hprop t ht).1.2.1
              set D := (∑ j, (yseq t j : ℂ) • A j - C) * mmwuIterate η M t
              have htr1 : ((∑ j, (yseq t j : ℂ) • A j - C) *
                  ((R : ℂ) • mmwuIterate η M t)).trace.re = R * D.trace.re := by
                rw [Algebra.mul_smul_comm, Matrix.trace_smul]
                simp [D, Complex.mul_re]
              have htr2 : (M t * mmwuIterate η M t).trace.re = w⁻¹ * D.trace.re := by
                change ((((w : ℂ)⁻¹) • (∑ j, (yseq t j : ℂ) • A j - C)) *
                  mmwuIterate η M t).trace.re = _
                rw [Algebra.smul_mul_assoc, Matrix.trace_smul]
                simp [D, ← Complex.ofReal_inv, Complex.mul_re]
              have htr : ((∑ j, (yseq t j : ℂ) • A j - C) *
                  ((R : ℂ) • mmwuIterate η M t)).trace.re =
                  w * R * (M t * mmwuIterate η M t).trace.re := by
                rw [htr1, htr2]
                field_simp [hw.ne']
              rw [htr] at hpic
              have hdiv : -(ε / 3) / (w * R) ≤ (M t * mmwuIterate η M t).trace.re :=
                (div_le_iff₀ (by positivity)).mpr (by linarith)
              linarith [show -(ε / 3) / (w * R) = -(ε / (3 * w * R)) by ring]
            rw [Matrix.trace_sum, Complex.re_sum]
            calc -(T : ℝ) * (ε / (3 * w * R))
                = ∑ _t ∈ Finset.Icc 1 T, -(ε / (3 * w * R)) := by
                  simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              _ ≤ ∑ t ∈ Finset.Icc 1 T, (M t * mmwuIterate η M t).trace.re :=
                  Finset.sum_le_sum hterm
          have hsq_ub : (∑ t ∈ Finset.Icc 1 T, M t ^ 2 * mmwuIterate η M t).trace.re ≤ T := by
            rw [Matrix.trace_sum, Complex.re_sum]
            calc (∑ t ∈ Finset.Icc 1 T, (M t ^ 2 * mmwuIterate η M t).trace.re)
                ≤ ∑ _t ∈ Finset.Icc 1 T, (1 : ℝ) :=
                  Finset.sum_le_sum fun t ht =>
                    trace_sq_mul_density_le_one (hMherm t ht) (hMnorm t ht) (hdens t ht)
              _ = T := by simp [Finset.sum_const, Nat.card_Icc]
          have hη_sum : η * (T : ℝ) + Real.log n / η ≤ 2 * (T : ℝ) * (ε / (3 * w * R)) := by
            have hηT : η * (T : ℝ) + Real.log n / η = 2 * (η * (T : ℝ)) := by
              have : Real.log n = η ^ 2 * (T : ℝ) := by
                rw [hη_sq, inv_mul_cancel_right₀ hTR_pos.ne']
              rw [this]
              field_simp [hη_pos.ne']
              ring
            have hη_le : η ≤ ε / (3 * w * R) := by
              have hsq_le : η ^ 2 ≤ (ε / (3 * w * R)) ^ 2 := by
                rw [hη_sq, div_pow, le_div_iff₀ (by positivity)]
                have hmul := mul_le_mul_of_nonneg_right hT_ge
                  (show 0 ≤ (T : ℝ)⁻¹ * ε ^ 2 by positivity)
                have hsimp1 : 9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹ * ((T : ℝ)⁻¹ * ε ^ 2) =
                    Real.log n * (T : ℝ)⁻¹ * (3 * w * R) ^ 2 := by
                  field_simp [hε.ne']
                  ring
                have hsimp2 : (T : ℝ) * ((T : ℝ)⁻¹ * ε ^ 2) = ε ^ 2 := by
                  field_simp [hTR_pos.ne']
                linarith
              exact (abs_le_of_sq_le_sq' hsq_le (by positivity)).2
            rw [hηT]
            nlinarith
          have hmin_ge : -(T : ℝ) * (ε / (w * R)) ≤ minEigenvalue S := by
            have h1 := mul_le_mul_of_nonneg_left hsq_ub hη_pos.le
            have h2 : -(T : ℝ) * (ε / (w * R)) =
                -(T : ℝ) * (ε / (3 * w * R)) - 2 * (T : ℝ) * (ε / (3 * w * R)) := by ring
            linarith
          have hmul := mul_le_mul_of_nonneg_left hmin_ge (show 0 ≤ w * (T : ℝ)⁻¹ by positivity)
          have hcancel : w * (T : ℝ)⁻¹ * (-(T : ℝ) * (ε / (w * R))) = -(ε * R⁻¹) := by
            field_simp [hw.ne', hR.ne', hTR_pos.ne']
          linarith
        · have hSn : specNorm S ≤ T := by
            calc specNorm S ≤ ∑ t ∈ Finset.Icc 1 T, specNorm (M t) := specNorm_sum_le _ _
              _ ≤ ∑ _t ∈ Finset.Icc 1 T, (1 : ℝ) := Finset.sum_le_sum hMnorm
              _ = T := by simp [Finset.sum_const, Nat.card_Icc]
          have hmin_ge : -(T : ℝ) ≤ minEigenvalue S :=
            (neg_le_neg hSn).trans (neg_specNorm_le_minEigenvalue hSherm (by simpa using hn0))
          have hmul := mul_le_mul_of_nonneg_left hmin_ge (show 0 ≤ w * (T : ℝ)⁻¹ by positivity)
          have hcancel : w * (T : ℝ)⁻¹ * -(T : ℝ) = -w := by
            field_simp [hTR_pos.ne']
          have hw_lt : w < ε * R⁻¹ := by
            rw [lt_mul_inv_iff₀ hR]
            linarith
          linarith
      refine ⟨⟨hy_nonneg, ?_⟩, hby_le⟩
      rw [hmat_eq]
      exact posSemidef_smul_add_one hn0 hSherm (w * (T : ℝ)⁻¹) (ε * R⁻¹) (by positivity) hminS
