-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P23.projectiveQubitEquality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:20:55.570876+00:00
-- url     : https://prove2.me/submissions/12a55682-d9ca-49df-8df6-51920910ddc3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder Kronecker

namespace X7Holevo

open QAlgorithms

variable {K : Type*} [Fintype K] {d : ℕ}

/-- The block of `X` at honest indices `(a,b)`. -/
def blk {a : ℕ} (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (x y : Fin a) :
    Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i i' => X (x, i) (y, i')

/-- The partial pairing with an effect. -/
def Ymat {a : ℕ} (Fk : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Matrix (Fin a) (Fin a) ℂ := Matrix.of fun x y => (Fk * blk X x y).trace

lemma idTensor_holevo {a : ℕ} (R F : K → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    idTensorSuperop (Entanglement.holevoMap R F) X = ∑ k, Ymat (F k) X ⊗ₖ R k := by
  ext p q
  simp [idTensorSuperop, Entanglement.holevoMap, Matrix.kronecker, Matrix.sum_apply, Ymat, blk,
    Matrix.kroneckerMap_apply]

def Vmat {a : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (l : Fin d) : Matrix (Fin a × Fin d) (Fin a) ℂ :=
  fun p b => if p.1 = b then star (B l p.2) else 0

lemma Ymat_eq {a : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Ymat (star B * B) X = ∑ l, (Vmat (a := a) B l)ᴴ * X * Vmat (a := a) B l := by
  ext x y
  simp only [Ymat, blk, Matrix.of_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.conjTranspose_apply, Vmat, Matrix.star_apply]
  simp only [Fintype.sum_prod_type_right]
  simp only [apply_ite star, star_star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

lemma Ymat_psd {a : ℕ} {Fk : Matrix (Fin d) (Fin d) ℂ} (hF : Fk.PosSemidef)
    {X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ} (hX : X.PosSemidef) : (Ymat Fk X).PosSemidef := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℂ, Fk = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hF.nonneg
  rw [hB, Ymat_eq]
  exact Matrix.posSemidef_sum _ (fun l _ => hX.conjTranspose_mul_mul_same _)

lemma holevo_cp (R F : K → Matrix (Fin d) (Fin d) ℂ) (hR : ∀ k, (R k).PosSemidef)
    (hF : ∀ k, (F k).PosSemidef) : Entanglement.IsCompletelyPositive (Entanglement.holevoMap R F) := by
  intro r X hX
  rw [idTensor_holevo]
  exact Matrix.posSemidef_sum _ (fun k _ => (Ymat_psd (hF k) hX).kronecker (hR k))

lemma holevo_eb [Fintype K] (R F : K → Matrix (Fin d) (Fin d) ℂ) (hR : ∀ k, IsDensityMatrix (R k))
    (hF : ∀ k, (F k).PosSemidef) : Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) := by
  intro a ha X hX
  rw [idTensor_holevo]
  let e := Fintype.equivFin K
  let D0 : Matrix (Fin a) (Fin a) ℂ := Matrix.diagonal (fun x => if x = ⟨0, ha⟩ then 1 else 0)
  have hD0 : IsDensityMatrix D0 := by
    refine ⟨?_, by simp [D0, Matrix.trace_diagonal]⟩
    rw [Matrix.posSemidef_diagonal_iff]
    intro x; split_ifs <;> norm_num
  let Y : K → Matrix (Fin a) (Fin a) ℂ := fun k => Ymat (F k) X
  have hY : ∀ k, (Y k).PosSemidef := fun k => Ymat_psd (hF k) hX.1
  refine ⟨Fintype.card K, fun j => (Y (e.symm j)).trace.re,
    fun j => if (Y (e.symm j)).trace = 0 then D0 else ((Y (e.symm j)).trace)⁻¹ • Y (e.symm j),
    fun j => R (e.symm j), fun j => ?_, fun j => ⟨?_, hR _⟩, ?_⟩
  · exact (RCLike.nonneg_iff.1 (hY _).trace_nonneg).1
  · dsimp only
    split_ifs with h
    · exact hD0
    · refine ⟨?_, ?_⟩
      · have hpos : 0 < (Y (e.symm j)).trace := lt_of_le_of_ne (hY _).trace_nonneg (Ne.symm h)
        exact (hY _).smul (inv_nonneg.2 hpos.le)
      · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ h]
  · rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    dsimp only
    split_ifs with h
    · have h0 : Ymat (F (e.symm j)) X = 0 := (hY _).trace_eq_zero_iff.1 h
      have h1 : (Y (e.symm j)).trace.re = 0 := by simp [h]
      rw [h1, h0]
      simp
    · have him : (Y (e.symm j)).trace.im = 0 := by
        have := (RCLike.nonneg_iff.1 (hY (e.symm j)).trace_nonneg).2
        simpa using this
      have hre : ((Y (e.symm j)).trace.re : ℂ) = (Y (e.symm j)).trace :=
        Complex.ext (by simp) (by simp [him])
      rw [hre]
      ext p q
      simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
      change Y (e.symm j) p.1 q.1 * _ = _
      field_simp

end X7Holevo

end


noncomputable section

open scoped Matrix ComplexOrder Kronecker

namespace X7P23

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23

lemma vn_sq {n : ℕ} (r : Fin n → ℝ) : vectorNorm r ^ 2 = ∑ i, r i ^ 2 := by
  unfold vectorNorm
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  simp

lemma vn_nonneg {n : ℕ} (r : Fin n → ℝ) : 0 ≤ vectorNorm r := norm_nonneg _

lemma vn_smul {n : ℕ} (a : ℝ) (r : Fin n → ℝ) : vectorNorm (a • r) = |a| * vectorNorm r := by
  unfold vectorNorm
  rw [show (WithLp.toLp 2 (a • r) : EuclideanSpace ℝ (Fin n)) = a • WithLp.toLp 2 r from rfl,
    norm_smul, Real.norm_eq_abs]

variable (B : BlochBasis 2)

/-- `Σ s_j λ_j`. -/
def S (s : BlochVector 2) : Operator 2 := ∑ j, (s j : ℂ) • B.generator j

lemma blochState_eq (s : BlochVector 2) : blochState B s = (1 / 2 : ℂ) • (1 + S B s) := by
  unfold blochState S
  rw [smul_add]
  norm_num

lemma trace_gen_S (i : BlochIndex 2) (s : BlochVector 2) :
    (B.generator i * S B s).trace = 2 * (s i : ℂ) := by
  simp only [S, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, B.normalized,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma trace_S (s : BlochVector 2) : (S B s).trace = 0 := by
  simp [S, Matrix.trace_sum, Matrix.trace_smul, B.traceless]

lemma trace_gen_state (i : BlochIndex 2) (s : BlochVector 2) :
    (B.generator i * blochState B s).trace = (s i : ℂ) := by
  rw [blochState_eq, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_add, trace_gen_S, B.traceless]
  simp only [smul_eq_mul]; ring

lemma trace_state (s : BlochVector 2) : (blochState B s).trace = 1 := by
  rw [blochState_eq, Matrix.trace_smul, Matrix.trace_add, trace_S]
  simp [Matrix.trace_one]

lemma S_herm (s : BlochVector 2) : (S B s).IsHermitian := by
  unfold S Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_smul, (B.hermitian j).eq]
  simp

lemma sq_traceless (T : Matrix (Fin 2) (Fin 2) ℂ) (h : T.trace = 0) :
    T * T = (T 0 0 * T 0 0 + T 0 1 * T 1 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.trace_fin_two] at h
  have h11 : T 1 1 = -T 0 0 := by linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11] <;> ring

lemma trace_S_mul (s : BlochVector 2) (M : Operator 2) :
    (S B s * M).trace = ∑ j, (s j : ℂ) * (B.generator j * M).trace := by
  simp only [S, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

lemma S_sq (s : BlochVector 2) :
    S B s * S B s = ((∑ j, s j ^ 2 : ℝ) : ℂ) • (1 : Operator 2) := by
  have h := sq_traceless (S B s) (trace_S B s)
  have htr : (S B s * S B s).trace = 2 * ((∑ j, s j ^ 2 : ℝ) : ℂ) := by
    rw [trace_S_mul]
    simp only [trace_gen_S]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [h] at htr ⊢
  rw [Matrix.trace_smul, Matrix.trace_one] at htr
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at htr
  congr 1
  linear_combination htr / 2

lemma state_herm (s : BlochVector 2) : (blochState B s).IsHermitian := by
  rw [blochState_eq]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, (S_herm B s).eq]
  simp

lemma state_idem (s : BlochVector 2) (hs : vectorNorm s = 1) :
    blochState B s * blochState B s = blochState B s := by
  have h1 : (∑ j, s j ^ 2 : ℝ) = 1 := by rw [← vn_sq, hs]; norm_num
  rw [blochState_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, S_sq, h1]
  simp only [Complex.ofReal_one, one_smul]
  rw [add_comm (S B s) 1, ← add_smul]
  norm_num

lemma state_psd (s : BlochVector 2) (hs : vectorNorm s = 1) : (blochState B s).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (blochState B s)
  rwa [(state_herm B s).eq, state_idem B s hs] at h

lemma state_density (s : BlochVector 2) (hs : vectorNorm s = 1) :
    IsDensityMatrix (blochState B s) := ⟨state_psd B s hs, trace_state B s⟩

lemma cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma sqrt_trace_of_sq {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (hN : N.IsHermitian) (c : ℝ) (hc : 0 ≤ c) (hNN : N * N = (c : ℂ) • N)
    (htr : N.trace.re = c) : (cfc Real.sqrt N).trace.re = Real.sqrt c := by
  rw [cfc_trace hN]
  have heig : ∀ i, hN.eigenvalues i * (hN.eigenvalues i - c) = 0 := by
    intro i
    have hv0 := hN.mulVec_eigenvectorBasis i
    have hv : N *ᵥ ⇑(hN.eigenvectorBasis i) =
        ((hN.eigenvalues i : ℝ) : ℂ) • ⇑(hN.eigenvectorBasis i) := by
      rw [hv0]; ext k; simp [Complex.real_smul]
    have h2 : (N * N) *ᵥ ⇑(hN.eigenvectorBasis i) =
        (((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • ⇑(hN.eigenvectorBasis i) := by
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul]
    have h2' : (N * N) *ᵥ ⇑(hN.eigenvectorBasis i) =
        ((c : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • ⇑(hN.eigenvectorBasis i) := by
      rw [hNN, Matrix.smul_mulVec, hv, smul_smul]
    have hne : (⇑(hN.eigenvectorBasis i) : n → ℂ) ≠ 0 := by
      intro h0
      have := (hN.eigenvectorBasis).orthonormal.1 i
      rw [show (hN.eigenvectorBasis i) = 0 from by
        ext k; exact congrFun h0 k] at this
      simp at this
    have h3 : ((((hN.eigenvalues i : ℝ) : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) -
        (c : ℂ) * ((hN.eigenvalues i : ℝ) : ℂ)) • (⇑(hN.eigenvectorBasis i) : n → ℂ) = 0 := by
      rw [sub_smul, ← h2, ← h2', sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · have : ((hN.eigenvalues i * (hN.eigenvalues i - c) : ℝ) : ℂ) = 0 := by
        push_cast; linear_combination h
      exact_mod_cast this
    · exact absurd h hne
  have hsum : ∑ i, hN.eigenvalues i = c := by
    rw [← htr, hN.trace_eq_sum_eigenvalues]
    simp
  simp only [Complex.re_sum, Complex.ofReal_re]
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0
    have : ∀ i, hN.eigenvalues i = 0 := fun i => by
      have := heig i; simp at this; exact this
    simp [this]
  · have : ∀ i, Real.sqrt (hN.eigenvalues i) = hN.eigenvalues i / Real.sqrt c := by
      intro i
      rcases mul_eq_zero.1 (heig i) with h | h
      · rw [h]; simp
      · rw [show hN.eigenvalues i = c by linarith]
        field_simp
        rw [Real.sq_sqrt hc]
    simp only [this, ← Finset.sum_div, hsum]
    field_simp
    rw [Real.sq_sqrt hc]

lemma nuclear_rank_one {n : ℕ} (u m : Fin n → ℝ) (hm : ∑ j, m j ^ 2 = 1) :
    nuclearNorm (fun i j => u i * m j) = Real.sqrt (∑ i, u i ^ 2) := by
  unfold nuclearNorm traceNorm
  set M : Matrix (Fin n) (Fin n) ℂ := (Matrix.of fun i j => u i * m j).map fun x => (x : ℂ) with hM
  set U : ℝ := ∑ i, u i ^ 2 with hU
  have hent : ∀ i j, (Mᴴ * M) i j = ((U * m i * m j : ℝ) : ℂ) := by
    intro i j
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      Complex.star_def, Complex.conj_ofReal, hU]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => by positivity)
  apply sqrt_trace_of_sq _ (Matrix.isHermitian_conjTranspose_mul_self M) U hU0
  · ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hent]
    simp only [hent, smul_eq_mul]
    push_cast
    have hm' : ∑ k, (m k : ℂ) ^ 2 = 1 := by exact_mod_cast hm
    calc ∑ k, (U : ℂ) * m i * m k * (U * m k * m j)
        = (U : ℂ) * m i * (U * m j) * ∑ k, (m k : ℂ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [hm']; ring
  · rw [Matrix.trace]
    simp only [Matrix.diag, hent]
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re]
    calc ∑ i, U * m i * m i = U * ∑ i, m i ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = U := by rw [hm, mul_one]

lemma rank_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0) : A.rank ≠ 0 := by
  intro h
  apply hA
  unfold Matrix.rank at h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

variable (m s1 s2 : BlochVector 2)

lemma phi_apply (X : Operator 2) : projectivePreparation B m s1 s2 X =
    (blochState B m * X).trace • blochState B s1 + (blochState B (-m) * X).trace • blochState B s2 := by
  simp [projectivePreparation, Entanglement.holevoMap, Fin.sum_univ_two]

lemma trace_state_gen (s : BlochVector 2) (j : BlochIndex 2) :
    (blochState B s * B.generator j).trace = (s j : ℂ) := by
  rw [Matrix.trace_mul_comm, trace_gen_state]

lemma blochC_proj : blochC B (projectivePreparation B m s1 s2) = (1 / 2 : ℝ) • (s1 + s2) := by
  funext i
  simp only [blochC, coordinates, phi_apply, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_state, Matrix.mul_add, Matrix.trace_add, trace_gen_state, smul_eq_mul]
  simp
  ring

lemma blochA_proj : blochA B (projectivePreparation B m s1 s2) =
    (fun i j => (1 / 2 : ℝ) * (s1 i - s2 i) * m j) := by
  funext i j
  simp only [blochA, phi_apply, trace_state_gen, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, trace_gen_state, smul_eq_mul]
  simp
  ring

end X7P23

namespace X7P23

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23

lemma S_neg (B : BlochBasis 2) (m : BlochVector 2) : S B (-m) = -S B m := by
  simp [S, Finset.sum_neg_distrib]

lemma state_add_neg (B : BlochBasis 2) (m : BlochVector 2) :
    blochState B m + blochState B (-m) = 1 := by
  rw [blochState_eq, blochState_eq, S_neg, ← smul_add]
  rw [show (1 : Operator 2) + S B m + (1 + -S B m) = (2 : ℂ) • 1 by rw [two_smul]; abel, smul_smul]
  norm_num

lemma sum_sq_of_vn {n : ℕ} (r : Fin n → ℝ) (h : vectorNorm r = 1) : ∑ i, r i ^ 2 = 1 := by
  rw [← vn_sq, h]; norm_num

end X7P23

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23 X7P23 in
theorem solution (B : BlochBasis 2) (m s1 s2 : BlochVector 2)
    (hm : vectorNorm m = 1) (hs1 : vectorNorm s1 = 1) (hs2 : vectorNorm s2 = 1) :
    let Phi := projectivePreparation B m s1 s2
    let A := blochA B Phi
    let c := blochC B Phi
    IsCPTP Phi ∧ Entanglement.IsEntanglementBreakingPositive Phi ∧
    c = (1 / 2 : ℝ) • (s1 + s2) ∧
    A = (fun i j => (1 / 2 : ℝ) * (s1 i - s2 i) * m j) ∧
    vectorNorm (s1 - c) = (1 / 2 : ℝ) * vectorNorm (s1 - s2) ∧
    vectorNorm (s2 - c) = (1 / 2 : ℝ) * vectorNorm (s1 - s2) ∧
    A.rank ≤ 1 ∧ (s1 ≠ s2 → A.rank = 1) ∧
    nuclearNorm A ^ 2 + vectorNorm c ^ 2 =
      (1 / 4 : ℝ) * (vectorNorm (s1 - s2) ^ 2 + vectorNorm (s1 + s2) ^ 2) ∧
    nuclearNorm A ^ 2 + vectorNorm c ^ 2 = 1 ∧
    (c ≠ 0 ↔ s1 + s2 ≠ 0) := by
  intro Phi A c
  have hc : c = (1 / 2 : ℝ) • (s1 + s2) := blochC_proj B m s1 s2
  have hA : A = (fun i j => (1 / 2 : ℝ) * (s1 i - s2 i) * m j) := blochA_proj B m s1 s2
  have hm2 := sum_sq_of_vn m hm
  have h12 := sum_sq_of_vn s1 hs1
  have h22 := sum_sq_of_vn s2 hs2
  have hnegm : vectorNorm (-m) = 1 := by
    rw [show -m = (-1 : ℝ) • m by simp, vn_smul, hm]; norm_num
  have hnuc : nuclearNorm A = Real.sqrt (∑ i, ((1 / 2 : ℝ) * (s1 i - s2 i)) ^ 2) := by
    rw [hA]; exact nuclear_rank_one (fun i => (1 / 2 : ℝ) * (s1 i - s2 i)) m hm2
  have hnuc2 : nuclearNorm A ^ 2 = ∑ i, ((1 / 2 : ℝ) * (s1 i - s2 i)) ^ 2 := by
    rw [hnuc, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  have hR : ∀ k, IsDensityMatrix ((![blochState B s1, blochState B s2] : Fin 2 → Operator 2) k) := by
    intro k; fin_cases k
    · exact state_density B s1 hs1
    · exact state_density B s2 hs2
  have hF : ∀ k, ((![blochState B m, blochState B (-m)] : Fin 2 → Operator 2) k).PosSemidef := by
    intro k; fin_cases k
    · exact state_psd B m hm
    · exact state_psd B (-m) hnegm
  have hkey : nuclearNorm A ^ 2 + vectorNorm c ^ 2 =
      (1 / 4 : ℝ) * (vectorNorm (s1 - s2) ^ 2 + vectorNorm (s1 + s2) ^ 2) := by
    rw [hnuc2, vn_sq, vn_sq, vn_sq, hc]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  refine ⟨⟨X7Holevo.holevo_cp _ _ (fun k => (hR k).1) hF, fun X => ?_⟩,
    X7Holevo.holevo_eb _ _ hR hF, hc, hA, ?_, ?_, ?_, ?_, hkey, ?_, ?_⟩
  · show (projectivePreparation B m s1 s2 X).trace = X.trace
    rw [phi_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_state, trace_state,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← Matrix.trace_add, ← Matrix.add_mul,
      state_add_neg, Matrix.one_mul]
  · rw [hc, show s1 - (1 / 2 : ℝ) • (s1 + s2) = (1 / 2 : ℝ) • (s1 - s2) by
      funext i; simp; ring, vn_smul]
    norm_num
  · rw [hc, show s2 - (1 / 2 : ℝ) • (s1 + s2) = (-1 / 2 : ℝ) • (s1 - s2) by
      funext i; simp; ring, vn_smul]
    norm_num
  · rw [hA]
    exact Matrix.rank_vecMulVec_le (fun i => (1 / 2 : ℝ) * (s1 i - s2 i)) m
  · intro hne
    have hle : A.rank ≤ 1 := by
      rw [hA]; exact Matrix.rank_vecMulVec_le (fun i => (1 / 2 : ℝ) * (s1 i - s2 i)) m
    have hA0 : A ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, s1 i ≠ s2 i := by
        by_contra h; push Not at h; exact hne (funext h)
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra h; push Not at h; simp [h] at hm2
      intro h0
      have := congrFun (congrFun h0 i) j
      rw [hA] at this
      simp only [Matrix.zero_apply] at this
      have : (s1 i - s2 i) * m j = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact hi (by linarith)
      · exact hj h
    have := X7P23.rank_ne_zero A hA0
    omega
  · rw [hkey, vn_sq, vn_sq]
    simp only [Pi.add_apply, Pi.sub_apply]
    have : ∑ i, (s1 i - s2 i) ^ 2 + ∑ i, (s1 i + s2 i) ^ 2 = 2 * ∑ i, s1 i ^ 2 + 2 * ∑ i, s2 i ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, h12, h22]; norm_num
  · rw [hc]
    constructor
    · intro h h0; apply h; rw [h0, smul_zero]
    · intro h h0; apply h
      have := congrArg (fun v => (2 : ℝ) • v) h0
      simpa [smul_smul] using this
