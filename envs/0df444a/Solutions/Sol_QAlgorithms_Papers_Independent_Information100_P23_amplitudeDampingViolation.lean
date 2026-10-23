-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P23.amplitudeDampingViolation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:27:39.775027+00:00
-- url     : https://prove2.me/submissions/9e9708f6-0f91-41b7-a683-c41a6381557e

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

namespace X7KADc

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


end X7KADc

namespace X7KAD

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23

lemma anticomm (T U : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.trace = 0) (hU : U.trace = 0) :
    T * U + U * T = (T * U).trace • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.trace_fin_two] at hT hU
  have hT11 : T 1 1 = -T 0 0 := by linear_combination hT
  have hU11 : U 1 1 = -U 0 0 := by linear_combination hU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hT11, hU11, Matrix.trace_fin_two] <;> ring

variable (B : BlochBasis 2)

lemma gen_sq (i : BlochIndex 2) : B.generator i * B.generator i = 1 := by
  have h := anticomm _ _ (B.traceless i) (B.traceless i)
  rw [B.normalized i i, if_pos rfl, ← two_smul ℂ (B.generator i * B.generator i)] at h
  have h2 := congrArg (fun M => (1 / 2 : ℂ) • M) h
  simp only [smul_smul] at h2
  norm_num at h2
  exact h2

lemma gen_anti (i j : BlochIndex 2) (hij : i ≠ j) :
    B.generator i * B.generator j = -(B.generator j * B.generator i) := by
  have h := anticomm _ _ (B.traceless i) (B.traceless j)
  rw [B.normalized i j, if_neg hij, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h


def ix : BlochIndex 2 := ⟨0, by decide⟩
def iy : BlochIndex 2 := ⟨1, by decide⟩
def iz : BlochIndex 2 := ⟨2, by decide⟩

lemma univ_eq : (Finset.univ : Finset (BlochIndex 2)) = {ix, iy, iz} := by decide

lemma sum3 {M : Type*} [AddCommMonoid M] (f : BlochIndex 2 → M) :
    ∑ i, f i = f ix + f iy + f iz := by
  rw [univ_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-- the linear reconstruction map -/
def Rlin : Operator 2 →ₗ[ℂ] Operator 2 :=
  (1 / 2 : ℂ) • (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight (1 : Operator 2) +
  ∑ i, (1 / 2 : ℂ) • ((Matrix.traceLinearMap (Fin 2) ℂ ℂ) ∘ₗ
    LinearMap.mulLeft ℂ (B.generator i)).smulRight (B.generator i)

lemma Rlin_apply (X : Operator 2) : Rlin B X =
    (X.trace / 2) • 1 + ∑ i, ((B.generator i * X).trace / 2) • B.generator i := by
  simp [Rlin, LinearMap.sum_apply, smul_smul, div_eq_inv_mul]

lemma trace_herm_real {X : Operator 2} (hX : X.IsHermitian) : ((X.trace.re : ℝ) : ℂ) = X.trace := by
  have h : star X.trace = X.trace := by rw [← Matrix.trace_conjTranspose, hX.eq]
  exact Complex.conj_eq_iff_re.mp h

lemma trace_gen_herm_real (i : BlochIndex 2) {X : Operator 2} (hX : X.IsHermitian) :
    (((B.generator i * X).trace.re : ℝ) : ℂ) = (B.generator i * X).trace := by
  have h : star (B.generator i * X).trace = (B.generator i * X).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq, (B.hermitian i).eq,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp h

lemma Rlin_herm {H : Operator 2} (hH : H.IsHermitian) : Rlin B H = H := by
  set H' := H - (H.trace / 2) • (1 : Operator 2) with hH'
  have hreal := trace_herm_real hH
  have h1 : H'.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH', Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
    congr 2
    rw [← hreal]
    simp [Complex.conj_ofReal]
  have h2 : H'.trace = 0 := by
    rw [hH', Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp
  have hrec := B.reconstruction H' h1 h2
  have hg : ∀ i, (B.generator i * H').trace = (B.generator i * H).trace := by
    intro i
    rw [hH', Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_one,
      B.traceless]
    simp
  simp only [hg, trace_gen_herm_real B _ hH] at hrec
  rw [Rlin_apply]
  have : H = (H.trace / 2) • (1 : Operator 2) + H' := by rw [hH']; abel
  conv_rhs => rw [this, hrec]
  rw [Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]
  congr 1
  ring

lemma Rlin_id (X : Operator 2) : Rlin B X = X := by
  set H1 : Operator 2 := (1 / 2 : ℂ) • (X + Xᴴ)
  set H2 : Operator 2 := (-Complex.I / 2) • (X - Xᴴ)
  have h1 : H1.IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [H1, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  have h2 : H2.IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [H2, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      simp [Complex.conj_I]; ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  have hX : X = H1 + Complex.I • H2 := by
    simp only [H1, H2, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]; ring
  have key : Rlin B (H1 + Complex.I • H2) = H1 + Complex.I • H2 := by
    rw [map_add, Rlin_herm B h1, LinearMap.map_smul_of_tower, Rlin_herm B h2]
  rw [← hX] at key
  exact key

lemma decomp (X : Operator 2) :
    X = (X.trace / 2) • 1 + ∑ i, ((B.generator i * X).trace / 2) • B.generator i := by
  rw [← Rlin_apply, Rlin_id]

lemma chan_ext (Φ Ψ : ChannelMap 2) (h1 : Φ 1 = Ψ 1) (hg : ∀ i, Φ (B.generator i) = Ψ (B.generator i)) :
    Φ = Ψ := by
  ext1 X
  rw [decomp B X]
  simp only [map_add, map_sum, map_smul, h1, hg]

lemma affine_one (c : BlochVector 2) (A : BlochMatrix 2) :
    affineMap B c A 1 = 1 + ∑ i, (c i : ℂ) • B.generator i := by
  simp [affineMap, Matrix.trace_one, B.traceless]

lemma affine_gen (c : BlochVector 2) (A : BlochMatrix 2) (k : BlochIndex 2) :
    affineMap B c A (B.generator k) = ∑ i, (A i k : ℂ) • B.generator i := by
  simp [affineMap, B.traceless, B.normalized]

lemma affine_trace (c : BlochVector 2) (A : BlochMatrix 2) (X : Operator 2) :
    (affineMap B c A X).trace = X.trace := by
  simp [affineMap, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, B.traceless, Matrix.trace_one]


lemma idx_cases (i : BlochIndex 2) : i = ix ∨ i = iy ∨ i = iz := by
  revert i; decide

/-- Kraus conjugation map. -/
def kr (K : Operator 2) : ChannelMap 2 where
  toFun X := K * X * Kᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

lemma kr_apply (K X : Operator 2) : kr K X = K * X * Kᴴ := rfl

def gx : Operator 2 := B.generator ix
def gy : Operator 2 := B.generator iy
def gz : Operator 2 := B.generator iz
def P : Operator 2 := (1 / 2 : ℂ) • (1 + gz B)
def Q : Operator 2 := (1 / 2 : ℂ) • (1 - gz B)

lemma gz_sq : gz B * gz B = 1 := gen_sq B iz
lemma gx_sq : gx B * gx B = 1 := gen_sq B ix

lemma P_herm : (P B)ᴴ = P B := by
  simp [P, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, gz, (B.hermitian iz).eq]
lemma Q_herm : (Q B)ᴴ = Q B := by
  simp [Q, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, gz, (B.hermitian iz).eq]
lemma gx_herm : (gx B)ᴴ = gx B := (B.hermitian ix).eq

lemma PP : P B * P B = P B := by
  simp only [P, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, gz_sq, smul_smul]; module
lemma QQ : Q B * Q B = Q B := by
  simp only [Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, gz_sq, smul_smul]; module
lemma PQ : P B * Q B = 0 := by
  simp only [P, Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, gz_sq, smul_smul]; module
lemma QP : Q B * P B = 0 := by
  simp only [P, Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, gz_sq, smul_smul]; module
lemma PaddQ : P B + Q B = 1 := by
  simp only [P, Q]; module
lemma gzP : gz B * P B = P B := by
  simp only [P, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, gz_sq]; module
lemma gzQ : gz B * Q B = -Q B := by
  simp only [Q, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, gz_sq]; module
lemma Pgz : P B * gz B = P B := by
  simp only [P, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, gz_sq]; module
lemma Qgz : Q B * gz B = -Q B := by
  simp only [Q, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, gz_sq]; module

lemma gP (k : BlochIndex 2) (hk : k ≠ iz) : B.generator k * P B = Q B * B.generator k := by
  simp only [P, Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_one, gz, gen_anti B k iz hk]; module
lemma gQ (k : BlochIndex 2) (hk : k ≠ iz) : B.generator k * Q B = P B * B.generator k := by
  simp only [P, Q, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_one, gz, gen_anti B k iz hk]; module


lemma QaddP : Q B + P B = 1 := by rw [add_comm, PaddQ]
lemma one_eq : (1 : Operator 2) = P B + Q B := (PaddQ B).symm
lemma gz_eq : gz B = P B - Q B := by simp only [P, Q]; module

lemma PP' (w : Operator 2) : P B * (P B * w) = P B * w := by rw [← Matrix.mul_assoc, PP]
lemma QQ' (w : Operator 2) : Q B * (Q B * w) = Q B * w := by rw [← Matrix.mul_assoc, QQ]
lemma PQ' (w : Operator 2) : P B * (Q B * w) = 0 := by rw [← Matrix.mul_assoc, PQ, Matrix.zero_mul]
lemma QP' (w : Operator 2) : Q B * (P B * w) = 0 := by rw [← Matrix.mul_assoc, QP, Matrix.zero_mul]
lemma gzP' (w : Operator 2) : gz B * (P B * w) = P B * w := by rw [← Matrix.mul_assoc, gzP]
lemma gzQ' (w : Operator 2) : gz B * (Q B * w) = -(Q B * w) := by
  rw [← Matrix.mul_assoc, gzQ, Matrix.neg_mul]
lemma Pgz' (w : Operator 2) : P B * (gz B * w) = P B * w := by rw [← Matrix.mul_assoc, Pgz]
lemma Qgz' (w : Operator 2) : Q B * (gz B * w) = -(Q B * w) := by
  rw [← Matrix.mul_assoc, Qgz, Matrix.neg_mul]
lemma gP' (k : BlochIndex 2) (hk : k ≠ iz) (w : Operator 2) :
    B.generator k * (P B * w) = Q B * (B.generator k * w) := by
  rw [← Matrix.mul_assoc, gP B k hk, Matrix.mul_assoc]
lemma gQ' (k : BlochIndex 2) (hk : k ≠ iz) (w : Operator 2) :
    B.generator k * (Q B * w) = P B * (B.generator k * w) := by
  rw [← Matrix.mul_assoc, gQ B k hk, Matrix.mul_assoc]
lemma gg' (k : BlochIndex 2) (w : Operator 2) : B.generator k * (B.generator k * w) = w := by
  rw [← Matrix.mul_assoc, gen_sq, Matrix.one_mul]

def K0 (α : ℝ) : Operator 2 := P B + (α : ℂ) • Q B
def K1 (α : ℝ) : Operator 2 := ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • (P B * (B.generator ix * Q B))

lemma K0H (α : ℝ) : (K0 B α)ᴴ = K0 B α := by
  simp [K0, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, P_herm, Q_herm]
lemma K1H (α : ℝ) : (K1 B α)ᴴ = ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • (Q B * (B.generator ix * P B)) := by
  simp [K1, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, P_herm, Q_herm,
    (B.hermitian ix).eq, Matrix.mul_assoc]

lemma ixz : ix ≠ iz := by decide
lemma iyz : iy ≠ iz := by decide

lemma amp_one (α : ℝ) : amplitudeDamping B α 1 = 1 + ((1 - α ^ 2 : ℝ) : ℂ) • gz B := by
  rw [amplitudeDamping, affine_one, sum3]
  simp [ix, iy, iz, gz]

lemma amp_gen (α : ℝ) (k : BlochIndex 2) :
    amplitudeDamping B α (B.generator k) =
      (((![α, α, α ^ 2] : BlochVector 2) k : ℝ) : ℂ) • B.generator k := by
  rw [amplitudeDamping, affine_gen]
  simp [Matrix.diagonal_apply]

lemma amp_kraus (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    amplitudeDamping B α = kr (K0 B α) + kr (K1 B α) := by
  have hs : ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) =
      ((1 - α ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
  refine chan_ext B _ _ ?_ ?_
  · rw [amp_one, LinearMap.add_apply, kr_apply, kr_apply, K0H, K1H]
    simp only [K0, K1, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, PP', QQ', PQ', QP', PP, QQ, PQ, QP,
      gP' B ix ixz, gQ' B ix ixz, gP B ix ixz, gQ B ix ixz, gg', gen_sq, smul_zero, add_zero, zero_add,
      smul_smul]
    rw [gz_eq, one_eq B, hs]
    push_cast
    module
  · intro k
    rcases idx_cases k with rfl | rfl | rfl
    · rw [amp_gen, LinearMap.add_apply, kr_apply, kr_apply, K0H, K1H]
      simp only [K0, K1, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, PP', QQ', PQ', QP', PP, QQ, PQ, QP,
        gP' B ix ixz, gQ' B ix ixz, gP B ix ixz, gQ B ix ixz, gg', gen_sq, smul_zero, add_zero,
        zero_add, smul_smul, Matrix.mul_zero]
      rw [← smul_add, ← Matrix.add_mul, QaddP, Matrix.one_mul]
      rfl
    · rw [amp_gen, LinearMap.add_apply, kr_apply, kr_apply, K0H, K1H]
      simp only [K0, K1, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, PP', QQ', PQ', QP', PP, QQ, PQ, QP,
        gP' B ix ixz, gQ' B ix ixz, gP B ix ixz, gQ B ix ixz, gP' B iy iyz, gQ' B iy iyz,
        gP B iy iyz, gQ B iy iyz, gg', gen_sq, smul_zero, add_zero,
        zero_add, smul_smul, Matrix.mul_zero]
      rw [← smul_add, ← Matrix.add_mul, QaddP, Matrix.one_mul]
      rfl
    · rw [amp_gen, LinearMap.add_apply, kr_apply, kr_apply, K0H, K1H]
      rw [show B.generator iz = gz B from rfl]
      simp only [K0, K1, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, PP', QQ', PQ', QP', PP, QQ, PQ, QP,
        gP' B ix ixz, gQ' B ix ixz, gP B ix ixz, gQ B ix ixz, gg', gen_sq, smul_zero, add_zero,
        zero_add, smul_smul, Matrix.mul_zero, gzP', gzQ', Pgz', Qgz', gzP, gzQ, Pgz, Qgz,
        Matrix.mul_neg, Matrix.neg_mul, smul_neg, neg_zero]
      rw [hs, gz_eq, show ((![α, α, α ^ 2] : BlochVector 2) iz) = α ^ 2 from rfl]
      push_cast
      module


lemma idT_add (Φ Ψ : ChannelMap 2) {r : ℕ} (X : Matrix (Fin r × Fin 2) (Fin r × Fin 2) ℂ) :
    idTensorSuperop (⇑(Φ + Ψ)) X = idTensorSuperop (⇑Φ) X + idTensorSuperop (⇑Ψ) X := by
  ext p q
  simp [idTensorSuperop]

lemma idT_kr (K : Operator 2) {r : ℕ} (X : Matrix (Fin r × Fin 2) (Fin r × Fin 2) ℂ) :
    idTensorSuperop (⇑(kr K)) X =
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K) * X * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K)ᴴ := by
  show idTensorSuperop (fun Y : Operator 2 => K * Y * Kᴴ) X = _
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [idTensorSuperop, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  simp [ite_mul, apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_add_distrib, Finset.sum_ite_eq]

lemma kr_cp (K : Operator 2) : Entanglement.IsCompletelyPositive (kr K) := by
  intro r X hX
  rw [idT_kr]
  exact hX.mul_mul_conjTranspose_same _

lemma amp_cptp (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : IsCPTP (amplitudeDamping B α) := by
  refine ⟨?_, fun X => affine_trace B _ _ X⟩
  rw [amp_kraus B α h0 h1]
  intro r X hX
  rw [idT_add]
  exact (kr_cp _ r X hX).add (kr_cp _ r X hX)

lemma blochA_affine (c : BlochVector 2) (A : BlochMatrix 2) : blochA B (affineMap B c A) = A := by
  ext i j
  simp [blochA, affine_gen, Matrix.mul_sum, Matrix.trace_sum, B.normalized]

lemma blochC_affine (c : BlochVector 2) (A : BlochMatrix 2) : blochC B (affineMap B c A) = c := by
  ext i
  simp only [blochC, coordinates, LinearMap.map_smul_of_tower, affine_one]
  simp [Matrix.mul_add, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_add, B.normalized, B.traceless]
  ring

@[simp] lemma v_ix {R : Type*} (a b c : R) : (![a, b, c] : BlochIndex 2 → R) ix = a := rfl
@[simp] lemma v_iy {R : Type*} (a b c : R) : (![a, b, c] : BlochIndex 2 → R) iy = b := rfl
@[simp] lemma v_iz {R : Type*} (a b c : R) : (![a, b, c] : BlochIndex 2 → R) iz = c := rfl

lemma amp0_apply (X : Operator 2) :
    amplitudeDamping B 0 X = X.trace • blochState B ![0, 0, 1] := by
  simp [amplitudeDamping, affineMap, blochState, sum3, Matrix.diagonal_apply]
  module

open scoped MatrixOrder in
lemma nuc_diag (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) :
    nuclearNorm (Matrix.diagonal v) = ∑ i, v i := by
  unfold nuclearNorm traceNorm
  set N : Matrix (Fin 3) (Fin 3) ℂ := (Matrix.diagonal v).map fun x => (x : ℂ) with hN
  have hN' : N = Matrix.diagonal (fun i => (v i : ℂ)) := by
    rw [hN]; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  have hpsd : N.PosSemidef := by
    rw [hN', Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast hv i
  have hH : Nᴴ = N := hpsd.1.eq
  have hsq := CFC.sqrt_eq_real_sqrt (N * N) (by
    have := Matrix.posSemidef_conjTranspose_mul_self N
    rw [hH] at this
    exact this.nonneg)
  rw [cfcₙ_eq_cfc (hf0 := by simp), CFC.sqrt_mul_self N hpsd.nonneg] at hsq
  rw [hH, ← hsq, hN']
  simp [Matrix.trace_diagonal]


/-- partial transpose on the first factor -/
def PT (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => M (q.1, p.2) (p.1, q.2)

lemma PT_sum {q : ℕ} (M : Fin q → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    PT (∑ j, M j) = ∑ j, PT (M j) := by
  ext a b; simp [PT, Matrix.sum_apply]

lemma PT_kron (w : ℂ) (A C : Matrix (Fin 2) (Fin 2) ℂ) :
    PT (w • Matrix.kronecker A C) = w • Matrix.kronecker Aᵀ C := by
  ext a b; simp [PT, Matrix.kronecker, Matrix.kroneckerMap_apply]

lemma witness_nonneg (φ : Fin 2 × Fin 2 → ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : Entanglement.IsSeparablePositive M) : 0 ≤ star φ ⬝ᵥ (PT M *ᵥ φ) := by
  obtain ⟨q, w, A, C, hw, hAC, rfl⟩ := hM
  rw [PT_sum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_nonneg (fun j _ => ?_)
  rw [PT_kron]
  have hpsd : (((w j : ℝ) : ℂ) • Matrix.kronecker (A j)ᵀ (C j)).PosSemidef :=
    ((hAC j).1.1.transpose.kronecker (hAC j).2.1).smul (by exact_mod_cast hw j)
  exact hpsd.dotProduct_mulVec_nonneg φ

lemma W_formula (φ : Fin 2 → Fin 2 → ℂ) (a : Fin 2 → Fin 2 → Fin 2 → ℂ) (c : ℂ)
    (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hY : ∀ y i x j, Y (y, i) (x, j) = c * ∑ m, a m y i * star (a m x j)) :
    star (fun p : Fin 2 × Fin 2 => φ p.1 p.2) ⬝ᵥ (PT Y *ᵥ (fun p => φ p.1 p.2)) =
      c * ∑ m, ∑ x, ∑ y, (star (φ x) ⬝ᵥ a m y) * (star (a m x) ⬝ᵥ φ y) := by
  simp only [dotProduct, Matrix.mulVec, PT, Matrix.of_apply, hY, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply]
  ring

lemma kr_vmv (K : Operator 2) (a b : Fin 2 → ℂ) :
    kr K (Matrix.vecMulVec a (star b)) = Matrix.vecMulVec (K *ᵥ a) (star (K *ᵥ b)) := by
  rw [kr_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma star_mulVec_dot (M : Operator 2) (a b : Fin 2 → ℂ) :
    star (M *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (Mᴴ *ᵥ b) := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

lemma amp_not_eb (α : ℝ) (h0 : 0 < α) (h1 : α ≤ 1) :
    ¬ Entanglement.IsEntanglementBreakingPositive (amplitudeDamping B α) := by
  intro hEB
  -- an eigenvector of P
  have htrP : (P B).trace = 1 := by
    simp [P, Matrix.trace_add, Matrix.trace_smul, gz, B.traceless, Matrix.trace_one]
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, P B *ᵥ Pi.single k 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have : P B = 0 := by
      ext i k
      have := congrFun (h k) i
      simpa [Matrix.mulVec_single] using this
    rw [this] at htrP; simp at htrP
  set v : Fin 2 → ℂ := P B *ᵥ Pi.single k 1 with hvdef
  have hPv : P B *ᵥ v = v := by rw [hvdef, Matrix.mulVec_mulVec, PP]
  have hQv : Q B *ᵥ v = 0 := by rw [← hPv, Matrix.mulVec_mulVec, QP, Matrix.zero_mulVec]
  set u : Fin 2 → ℂ := B.generator ix *ᵥ v with hudef
  have hQu : Q B *ᵥ u = u := by
    have e : B.generator ix *ᵥ v = Q B *ᵥ (B.generator ix *ᵥ v) := by
      conv_lhs => rw [← hPv]
      rw [Matrix.mulVec_mulVec, gP B ix ixz, ← Matrix.mulVec_mulVec]
    rw [hudef, e, Matrix.mulVec_mulVec, QQ]
  have hPu : P B *ᵥ u = 0 := by
    rw [← hQu, Matrix.mulVec_mulVec, PQ, Matrix.zero_mulVec]
  have hgu : B.generator ix *ᵥ u = v := by
    rw [hudef, Matrix.mulVec_mulVec, gen_sq, Matrix.one_mulVec]
  set γ : ℝ := 1 - α ^ 2 with hγ
  set sq : ℂ := ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) with hsq
  have hs : sq * sq = (γ : ℂ) := by
    rw [hsq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
  have hK0v : K0 B α *ᵥ v = v := by
    rw [K0, Matrix.add_mulVec, Matrix.smul_mulVec, hPv, hQv, smul_zero, add_zero]
  have hK0u : K0 B α *ᵥ u = (α : ℂ) • u := by
    rw [K0, Matrix.add_mulVec, Matrix.smul_mulVec, hPu, hQu, zero_add]
  have hK1v : K1 B α *ᵥ v = 0 := by
    rw [K1, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv]; simp
  have hK1u : K1 B α *ᵥ u = sq • v := by
    rw [K1, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQu, hgu, hPv]
  -- inner products
  set n : ℂ := star v ⬝ᵥ v with hn
  have hvu : star v ⬝ᵥ u = 0 := by
    have := star_mulVec_dot (Q B) v u
    rw [Q_herm, hQv, hQu] at this
    simpa using this.symm
  have huv : star u ⬝ᵥ v = 0 := by
    rw [hudef, star_mulVec_dot, (B.hermitian ix).eq, ← hudef, hvu]
  have huu : star u ⬝ᵥ u = n := by
    rw [hudef, star_mulVec_dot, (B.hermitian ix).eq, Matrix.mulVec_mulVec, gen_sq, Matrix.one_mulVec]
  have hn0 : n ≠ 0 := by
    rw [hn]; intro h
    rw [dotProduct_star_self_eq_zero] at h
    exact hk h
  have hnnn : 0 ≤ n := dotProduct_star_self_nonneg v
  obtain ⟨nr, hnr⟩ : ∃ nr : ℝ, n = (nr : ℂ) := ⟨n.re, by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.1 hnnn).2.symm]⟩
  have hnrpos : 0 < nr := by
    have h1' : (0 : ℂ) ≤ (nr : ℂ) := hnr ▸ hnnn
    have h2' : (nr : ℂ) ≠ 0 := hnr ▸ hn0
    have := Complex.zero_le_real.1 h1'
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) h2'
  let ψ : Fin 2 → Fin 2 → ℂ := ![v, u]
  let Ψ : Fin 2 × Fin 2 → ℂ := fun p => ψ p.1 p.2
  let c : ℂ := ((1 / (2 * nr) : ℝ) : ℂ)
  have hc0 : 0 ≤ c := Complex.zero_le_real.2 (by positivity)
  let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := c • Matrix.vecMulVec Ψ (star Ψ)
  have hXtr : X.trace = c * (n + star u ⬝ᵥ u) := by
    simp [X, Ψ, ψ, Matrix.trace, Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, hn,
      dotProduct]
    ring
  have hX : IsDensityMatrix X := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star Ψ).smul hc0, ?_⟩
    rw [hXtr, huu, hnr]
    simp only [c]
    push_cast
    field_simp
    ring
  have hsep := hEB 2 (by norm_num) X hX
  rw [amp_kraus B α h0.le h1] at hsep
  let a : Fin 2 → Fin 2 → Fin 2 → ℂ := fun m y => (![K0 B α, K1 B α] m) *ᵥ ψ y
  have hY : ∀ y i x j, idTensorSuperop (⇑(kr (K0 B α) + kr (K1 B α))) X (y, i) (x, j) =
      c * ∑ m, a m y i * star (a m x j) := by
    intro y i x j
    have hblk : (Matrix.of fun i i' => X (y, i) (x, i')) = c • Matrix.vecMulVec (ψ y) (star (ψ x)) := by
      ext i' j'; simp [X, Ψ, Matrix.vecMulVec_apply]
    show (kr (K0 B α) + kr (K1 B α)) (Matrix.of fun i i' => X (y, i) (x, i')) i j = _
    rw [hblk, map_smul, LinearMap.add_apply, kr_vmv, kr_vmv]
    simp only [a, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply, smul_eq_mul]
  let φ : Fin 2 → Fin 2 → ℂ := ![u, -(α : ℂ) • v]
  have hW := witness_nonneg (fun p => φ p.1 p.2) _ hsep
  rw [W_formula φ a c _ hY] at hW
  have hsqs : star sq = sq := by rw [hsq]; exact Complex.conj_ofReal _
  have hαs : star (α : ℂ) = α := Complex.conj_ofReal _
  have hval : ∑ m, ∑ x, ∑ y, (star (φ x) ⬝ᵥ a m y) * (star (a m x) ⬝ᵥ φ y) =
      ((-(α ^ 2 * (1 + α ^ 2)) * nr ^ 2 : ℝ) : ℂ) := by
    simp only [Fin.sum_univ_two, a, φ, ψ, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hK0v, hK0u, hK1v, hK1u, star_smul, star_neg, star_zero, dotProduct_smul,
      smul_dotProduct, neg_dotProduct, dotProduct_neg, zero_dotProduct, dotProduct_zero, hvu, huv,
      huu, ← hn, smul_eq_mul, hsqs, hαs]
    rw [hγ] at hs
    rw [hnr]
    push_cast at hs ⊢
    linear_combination ((α : ℂ) ^ 2 * (nr : ℂ) ^ 2) * hs
  rw [hval] at hW
  simp only [c, ← Complex.ofReal_mul, Complex.zero_le_real] at hW
  have : 1 / (2 * nr) * (-(α ^ 2 * (1 + α ^ 2)) * nr ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by
      have : 0 < α ^ 2 * (1 + α ^ 2) * nr ^ 2 := by positivity
      linarith)
  linarith

end X7KAD

namespace X7KAD

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23 X7KADc

lemma amp0_eb (B : BlochBasis 2) :
    Entanglement.IsEntanglementBreakingPositive (amplitudeDamping B 0) := by
  have hn : vectorNorm (![0, 0, 1] : BlochVector 2) = 1 := by
    have h := vn_sq (![0, 0, 1] : BlochVector 2)
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
    simp at h
    have h0 := vn_nonneg (![0, 0, 1] : BlochVector 2)
    rcases h with h | h
    · exact h
    · linarith
  have heq : amplitudeDamping B 0 =
      Entanglement.holevoMap (K := Fin 1) (fun _ => blochState B ![0, 0, 1])
        (fun _ => (1 : Operator 2)) := by
    ext1 X
    rw [amp0_apply]
    simp [Entanglement.holevoMap]
  rw [heq]
  exact X7Holevo.holevo_eb _ _ (fun _ => state_density B _ hn) (fun _ => Matrix.PosSemidef.one)

end X7KAD

end

open scoped Matrix ComplexOrder

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P23 X7KAD X7KADc in
theorem solution (B : BlochBasis 2) (alpha : ℝ)
    (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    let Phi := amplitudeDamping B alpha
    IsCPTP Phi ∧
    blochA B Phi = Matrix.diagonal ![alpha, alpha, alpha ^ 2] ∧
    blochC B Phi = ![0, 0, 1 - alpha ^ 2] ∧
    nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 =
      1 + 2 * alpha ^ 2 + 4 * alpha ^ 3 + 2 * alpha ^ 4 ∧
    (0 < alpha → 1 < nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ∧
      ¬ Entanglement.IsEntanglementBreakingPositive Phi) ∧
    (alpha = 0 → Entanglement.IsEntanglementBreakingPositive Phi ∧
      nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 = 1 ∧
      ∀ X : Operator 2, Phi X = X.trace • blochState B ![0, 0, 1]) := by
  intro Phi
  have hA : blochA B Phi = Matrix.diagonal ![alpha, alpha, alpha ^ 2] := blochA_affine B _ _
  have hC : blochC B Phi = ![0, 0, 1 - alpha ^ 2] := blochC_affine B _ _
  have hnuc : nuclearNorm (blochA B Phi) = 2 * alpha + alpha ^ 2 := by
    rw [hA]
    have := nuc_diag ![alpha, alpha, alpha ^ 2] (by
      intro i; fin_cases i <;> simp <;> positivity)
    rw [Fin.sum_univ_three] at this
    simp at this
    rw [show (Matrix.diagonal ![alpha, alpha, alpha ^ 2] : BlochMatrix 2) =
      (Matrix.diagonal ![alpha, alpha, alpha ^ 2] : Matrix (Fin 3) (Fin 3) ℝ) from rfl]
    erw [this]; ring
  have hvec : vectorNorm (blochC B Phi) ^ 2 = (1 - alpha ^ 2) ^ 2 := by
    rw [hC, vn_sq, sum3]; simp
  have hsum : nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 =
      1 + 2 * alpha ^ 2 + 4 * alpha ^ 3 + 2 * alpha ^ 4 := by
    rw [hnuc, hvec]; ring
  refine ⟨amp_cptp B alpha h0 h1, hA, hC, hsum, fun hpos => ⟨?_, amp_not_eb B alpha hpos h1⟩,
    fun h => ?_⟩
  · rw [hsum]; nlinarith [pow_pos hpos 2, pow_pos hpos 3, pow_pos hpos 4]
  · subst h
    refine ⟨amp0_eb B, by rw [hsum]; ring, fun X => amp0_apply B X⟩

end
