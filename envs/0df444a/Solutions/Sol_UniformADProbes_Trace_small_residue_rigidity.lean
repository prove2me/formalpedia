-- Prove2me | solution 1 for UniformADProbes.Trace.small_residue_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:33:39.885528+00:00
-- url     : https://prove2.me/submissions/55cf2fbd-3c65-4472-904d-5167ba62e5fb

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

section
set_option autoImplicit false
namespace Dev.RigiditySpec
open Matrix

theorem herm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) : B.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hB

theorem rayleigh_lower {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (u : Fin n → ℝ) :
    sInf (spectrum ℝ B) * (u ⬝ᵥ u) ≤ u ⬝ᵥ (B *ᵥ u) := by
  have hH := herm B hB
  have hfin : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum (A := B)
  set c := sInf (spectrum ℝ B) with hc
  have hps : (B - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq]; simp
    · intro a ha
      have : a + c ∈ spectrum ℝ B := by
        have h2 : a ∈ spectrum ℝ (B - algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) c) := by
          rwa [Algebra.algebraMap_eq_smul_one]
        rw [← spectrum.sub_singleton_eq] at h2
        obtain ⟨x, hx, y, hy, rfl⟩ := h2
        rw [Set.mem_singleton_iff] at hy
        subst hy
        simpa using hx
      have := csInf_le hfin.bddBelow this
      simp only [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      linarith
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hps).2 u
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul] at this
  linarith
theorem rayleigh_upper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (u : Fin n → ℝ) :
    u ⬝ᵥ (B *ᵥ u) ≤ sSup (spectrum ℝ B) * (u ⬝ᵥ u) := by
  have hH := herm B hB
  have hfin : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum (A := B)
  set c := sSup (spectrum ℝ B) with hc
  have hps : (c • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq]; simp
    · intro a ha
      have h2 : a ∈ spectrum ℝ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) c - B) := by
        rwa [Algebra.algebraMap_eq_smul_one]
      rw [← spectrum.singleton_sub_eq] at h2
      obtain ⟨y, hy, x, hx, rfl⟩ := h2
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have := le_csSup hfin.bddAbove hx
      simp only [Set.mem_ofPred_eq]
      linarith
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hps).2 u
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul] at this
  linarith

end Dev.RigiditySpec
end

section
set_option autoImplicit false
namespace Dev.RigidityTensor
open Matrix

/-- The action of `B` on the `r`-fold tensor power (functions of `r` indices). -/
def Tens {n r : ℕ} {R : Type} [CommRing R] [Algebra ℝ R] (B : Matrix (Fin n) (Fin n) ℝ)
    (w : (Fin r → Fin n) → R) : (Fin r → Fin n) → R :=
  fun I => ∑ a, ∑ j, B (I a) j • w (Function.update I a j)

theorem quad_split {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin r)
    (w1 w2 : (Fin r → Fin n) → ℝ) :
    ∑ I, w1 I * ∑ j, M (I a) j * w2 (Function.update I a j) =
    ∑ rest : ({j // j ≠ a} → Fin n), ∑ x, ∑ j, M x j *
      (w1 ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)) *
       w2 ((Equiv.piSplitAt a (fun _ => Fin n)).symm (j, rest))) := by
  rw [← (Equiv.piSplitAt a (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun rest _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)) a = x := by
    simp [Equiv.piSplitAt_symm_apply]
  have h2 : Function.update ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)) a j =
      (Equiv.piSplitAt a (fun _ => Fin n)).symm (j, rest) := by
    ext i
    by_cases hi : i = a
    · subst hi; simp [Equiv.piSplitAt_symm_apply]
    · simp [Equiv.piSplitAt_symm_apply, hi]
  rw [h1, h2]; ring

theorem dot_split {n r : ℕ} (a : Fin r) (w : (Fin r → Fin n) → ℝ) :
    w ⬝ᵥ w = ∑ rest : ({j // j ≠ a} → Fin n), ∑ x,
      w ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)) *
       w ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)) := by
  rw [dotProduct, ← (Equiv.piSplitAt a (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]

theorem top_dot {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w1 w2 : (Fin r → Fin n) → ℝ) :
    w1 ⬝ᵥ Tens B w2 = ∑ a, ∑ I, w1 I * ∑ j, B (I a) j * w2 (Function.update I a j) := by
  rw [dotProduct, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Tens, smul_eq_mul, Finset.mul_sum]

theorem top_lower {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (w : (Fin r → Fin n) → ℝ) :
    (r : ℝ) * sInf (spectrum ℝ B) * (w ⬝ᵥ w) ≤ w ⬝ᵥ Tens B w := by
  rw [top_dot]
  have : ∀ a : Fin r, sInf (spectrum ℝ B) * (w ⬝ᵥ w) ≤
      ∑ I, w I * ∑ j, B (I a) j * w (Function.update I a j) := by
    intro a
    rw [quad_split, dot_split a, Finset.mul_sum]
    refine Finset.sum_le_sum fun rest _ => ?_
    have := RigiditySpec.rayleigh_lower B hB
      (fun x => w ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)))
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at this ⊢
    refine this.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (r : ℝ) * sInf (spectrum ℝ B) * (w ⬝ᵥ w) = ∑ _a : Fin r, sInf (spectrum ℝ B) * (w ⬝ᵥ w) := by
        simp; ring
    _ ≤ _ := Finset.sum_le_sum fun a _ => this a

theorem top_upper {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (w : (Fin r → Fin n) → ℝ) :
    w ⬝ᵥ Tens B w ≤ (r : ℝ) * sSup (spectrum ℝ B) * (w ⬝ᵥ w) := by
  rw [top_dot]
  have : ∀ a : Fin r, ∑ I, w I * ∑ j, B (I a) j * w (Function.update I a j) ≤
      sSup (spectrum ℝ B) * (w ⬝ᵥ w) := by
    intro a
    rw [quad_split, dot_split a, Finset.mul_sum]
    refine Finset.sum_le_sum fun rest _ => ?_
    have := RigiditySpec.rayleigh_upper B hB
      (fun x => w ((Equiv.piSplitAt a (fun _ => Fin n)).symm (x, rest)))
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at this ⊢
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc _ ≤ ∑ _a : Fin r, sSup (spectrum ℝ B) * (w ⬝ᵥ w) := Finset.sum_le_sum fun a _ => this a
    _ = _ := by simp; ring

theorem top_symm {n r : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (w1 w2 : (Fin r → Fin n) → ℝ) : w1 ⬝ᵥ Tens H w2 = Tens H w1 ⬝ᵥ w2 := by
  rw [top_dot, dotProduct_comm, top_dot]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [quad_split, quad_split]
  refine Finset.sum_congr rfl fun rest _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  have : H j x = H x j := by
    have := congrFun (congrFun hH x) j
    simpa [Matrix.transpose_apply] using this
  rw [this]; ring

end Dev.RigidityTensor
end

section
set_option autoImplicit false
namespace Dev.RigidityDet
open Matrix Polynomial

def rowLin {R : Type} [CommRing R] {r : ℕ} (X : Matrix (Fin r) (Fin r) R) (a : Fin r) :
    (Fin r → R) →ₗ[R] R where
  toFun y := (X.updateRow a y).det
  map_add' u v := Matrix.det_updateRow_add X a u v
  map_smul' s u := by simpa using Matrix.det_updateRow_smul X a s u

theorem det_updateRow_expand {R : Type} [CommRing R] {r : ℕ} (X : Matrix (Fin r) (Fin r) R)
    (a : Fin r) (y : Fin r → R) :
    (X.updateRow a y).det = ∑ k, y k * X.adjugate k a := by
  have : y = ∑ k, y k • (Pi.single k (1 : R) : Fin r → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have h := congrArg (rowLin X a) this
  rw [map_sum] at h
  simp only [map_smul, rowLin, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.adjugate_apply]

/-- `d/ds det (X + sY)` at `s = 0`, row version. -/
theorem sum_det_updateRow {R : Type} [CommRing R] {r : ℕ} (X Y : Matrix (Fin r) (Fin r) R) :
    ∑ a, (X.updateRow a (Y a)).det = Matrix.trace (X.adjugate * Y) := by
  simp only [det_updateRow_expand, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring

theorem sum_det_updateCol {R : Type} [CommRing R] {r : ℕ} (X Y : Matrix (Fin r) (Fin r) R) :
    ∑ b, (X.updateCol b (fun k => Y k b)).det = Matrix.trace (X.adjugate * Y) := by
  have h : ∀ b, (X.updateCol b (fun k => Y k b)).det = ∑ k, X.adjugate b k * Y k b := by
    intro b
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    rfl
  simp only [h, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem derivative_det {R : Type} [CommRing R] {r : ℕ} (X : Matrix (Fin r) (Fin r) R[X]) :
    derivative X.det = ∑ b, (X.updateCol b (fun k => derivative (X k b))).det := by
  simp only [Matrix.det_apply', derivative_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [derivative_intCast_mul, derivative_prod_finset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have : ∀ i, X.updateCol b (fun k => derivative (X k b)) (σ i) i =
      Function.update (fun i => X (σ i) i) b (derivative (X (σ b) b)) i := by
    intro i
    by_cases h : i = b
    · subst h; simp
    · simp [Matrix.updateCol_ne h, h]
  simp only [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ b), Finset.sdiff_singleton_eq_erase, mul_comm]

end Dev.RigidityDet
end

section
set_option autoImplicit false
namespace Dev.RigidityId
open Matrix Polynomial Dev.RigidityTensor Dev.RigidityDet

/-- Plücker-type vector of the `r` columns of `F`: all `r × r` minors (indexed by row maps). -/
noncomputable def plu {n r : ℕ} {R : Type} [CommRing R] (F : Matrix (Fin n) (Fin r) R) :
    (Fin r → Fin n) → R := fun I => (F.submatrix I id).det

theorem plu_update {n r : ℕ} {R : Type} [CommRing R] (F : Matrix (Fin n) (Fin r) R)
    (I : Fin r → Fin n) (a : Fin r) (j : Fin n) :
    plu F (Function.update I a j) = ((F.submatrix I id).updateRow a (F j)).det := by
  unfold plu
  congr 1
  ext a' b
  by_cases h : a' = a
  · subst h; simp
  · simp [Matrix.updateRow_ne h, h]

theorem top_plu {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin r) ℝ[X])
    (I : Fin r → Fin n) :
    Tens B (plu F) I = ((F.submatrix I id).adjugate *
      ((B.map C * F).submatrix I id)).trace := by
  rw [← sum_det_updateRow]
  unfold Tens
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ∀ j, plu F (Function.update I a j) = rowLin (F.submatrix I id) a (F j) := by
    intro j; rw [plu_update]; rfl
  simp only [this]
  have h2 : (B.map C * F).submatrix I id a = ∑ j, B (I a) j • F j := by
    ext b
    simp [Matrix.mul_apply, Polynomial.smul_eq_C_mul]
  rw [h2]
  show _ = rowLin (F.submatrix I id) a _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 : B (I a) j • F j = (C (B (I a) j)) • F j := by
    ext b; simp [Polynomial.smul_eq_C_mul]
  rw [h3, map_smul, Polynomial.smul_eq_C_mul, smul_eq_mul]

/-- The (polynomial) differential operator `t ∂ + B + t H` applied column by column. -/
noncomputable def Dop {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin r) ℝ[X]) :
    Matrix (Fin n) (Fin r) ℝ[X] :=
  (X : ℝ[X]) • F.map derivative + B.map C * F + (X : ℝ[X]) • (H.map C * F)

theorem key_identity {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin r) ℝ[X])
    (I : Fin r → Fin n) :
    (X : ℝ[X]) * derivative (plu F I) + Tens B (plu F) I + (X : ℝ[X]) * Tens H (plu F) I =
      ((F.submatrix I id).adjugate * ((Dop B H F).submatrix I id)).trace := by
  have h1 : derivative (plu F I) =
      ((F.submatrix I id).adjugate * ((F.map derivative).submatrix I id)).trace := by
    unfold plu
    rw [derivative_det, ← sum_det_updateCol]
    rfl
  have hs : (Dop B H F).submatrix I id = (X : ℝ[X]) • (F.map derivative).submatrix I id +
      (B.map C * F).submatrix I id + (X : ℝ[X]) • (H.map C * F).submatrix I id := by
    ext a b; simp [Dop]
  rw [h1, top_plu, top_plu, hs, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

end Dev.RigidityId
end

section
set_option autoImplicit false
namespace Dev.RigidityLA
open Matrix

theorem la1 {K : Type} [Field K] {n s : ℕ} (A : Matrix (Fin n) (Fin s) K)
    (hA : LinearIndependent K (fun j => fun i => A i j)) :
    ∃ J : Fin s → Fin n, (A.submatrix J id).det ≠ 0 := by
  classical
  have hrank : A.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have := linearIndependent_iff_card_eq_finrank_span.mp hA
    rw [Set.finrank, Fintype.card_fin] at this
    exact this.symm
  have hspan : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank]; simp
  obtain ⟨κ, a, hinj, hsp, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a hinj
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = s := by
    have := linearIndependent_iff_card_eq_finrank_span.mp hli
    rw [Set.finrank, hsp, hspan] at this
    simpa using this
  let e : Fin s ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hl : LinearIndependent K (fun i : Fin s => A.row (a (e i))) :=
    hli.comp e e.injective
  have : (A.submatrix (a ∘ e) id).Nonsingular := by
    apply Matrix.Nonsingular.of_linearIndependent_row
    exact hl
  exact (Matrix.nonsingular_iff_det_ne_zero.mp this) 

/-- The matrix with first column `u` and remaining columns those of `A`. -/
def consCol {K : Type} {n r : ℕ} (u : Fin n → K) (A : Matrix (Fin n) (Fin r) K) :
    Matrix (Fin n) (Fin (r + 1)) K := Matrix.of fun k b => (Fin.cons (u k) (A k) : Fin (r + 1) → K) b

theorem laplace {K : Type} [CommRing K] {n r : ℕ} (u : Fin n → K) (A : Matrix (Fin n) (Fin r) K)
    (J : Fin (r + 1) → Fin n) :
    ((consCol u A).submatrix J id).det =
      ∑ a : Fin (r + 1), (-1) ^ (a : ℕ) * u (J a) * (A.submatrix (J ∘ a.succAbove) id).det := by
  rw [Matrix.det_succ_column _ 0]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ((consCol u A).submatrix J id).submatrix a.succAbove (0 : Fin (r + 1)).succAbove =
      A.submatrix (J ∘ a.succAbove) id := by
    ext i b
    simp [consCol, Fin.succAbove_zero]
  rw [this]
  simp [consCol]

theorem recover {K : Type} [Field K] {n r : ℕ} (A : Matrix (Fin n) (Fin r) K)
    (hA : LinearIndependent K (fun j => fun i => A i j)) (u : Fin n → K) :
    u ∈ Submodule.span K (Set.range (fun j => fun i => A i j)) ↔
      ∀ J : Fin (r + 1) → Fin n, ∑ a : Fin (r + 1),
        (-1) ^ (a : ℕ) * u (J a) * (A.submatrix (J ∘ a.succAbove) id).det = 0 := by
  constructor
  · intro hu J
    rw [← laplace, ← Matrix.exists_mulVec_eq_zero_iff]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
    refine ⟨Fin.cons (-1) c, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · ext a
      simp [Matrix.mulVec, dotProduct, consCol, Fin.sum_univ_succ]
      have := congrFun hc (J a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      simp only [mul_comm (A (J a) _)]; ring
  · intro h
    by_contra hu
    have hli : LinearIndependent K (fun j => fun i => (consCol u A) i j) := by
      have : (fun j => fun i => (consCol u A) i j) = (Fin.cons u (fun j => fun i => A i j)) := by
        ext j i
        refine Fin.cases ?_ ?_ j <;> simp [consCol]
      rw [this, linearIndependent_finCons]
      exact ⟨hA, hu⟩
    obtain ⟨J, hJ⟩ := la1 _ hli
    exact hJ (by rw [laplace]; exact h J)

end Dev.RigidityLA
end

section
set_option autoImplicit false
namespace Dev.RigidityCore
open Matrix Polynomial Dev.RigidityTensor

theorem coeff_tens {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (I : Fin r → Fin n) (k : ℕ) :
    (Tens B w I).coeff k = Tens B (fun J => (w J).coeff k) I := by
  simp [Tens, finset_sum_coeff, coeff_smul]

theorem natDegree_tens_le {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (l : ℕ) (h : ∀ I, (w I).natDegree ≤ l) (I : Fin r → Fin n) :
    (Tens B w I).natDegree ≤ l := by
  unfold Tens
  refine natDegree_sum_le_of_forall_le _ _ fun a _ => natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (natDegree_smul_le _ _).trans (h _)

/-- the operator `Q = t ∂ + B + t H` on a vector of polynomials -/
noncomputable def Qop {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (I : Fin r → Fin n) : ℝ[X] :=
  X * derivative (w I) + Tens B w I + X * Tens H w I

theorem coeff_Q_zero {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (I : Fin r → Fin n) :
    (Qop B H w I).coeff 0 = Tens B (fun J => (w J).coeff 0) I := by
  simp [Qop, coeff_tens]

theorem coeff_Q_succ {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (I : Fin r → Fin n) (m : ℕ) :
    (Qop B H w I).coeff (m + 1) = ((m : ℝ) + 1) * (w I).coeff (m + 1) +
      Tens B (fun J => (w J).coeff (m + 1)) I + Tens H (fun J => (w J).coeff m) I := by
  simp only [Qop, coeff_add, coeff_X_mul, coeff_derivative, coeff_tens]
  ring

theorem natDegree_Q_le {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (w : (Fin r → Fin n) → ℝ[X])
    (l : ℕ) (h : ∀ I, (w I).natDegree ≤ l) (I : Fin r → Fin n) :
    (Qop B H w I).natDegree ≤ l + 1 := by
  unfold Qop
  have h1 : (X * derivative (w I)).natDegree ≤ l + 1 := by
    refine (natDegree_mul_le).trans ?_
    have := (natDegree_derivative_le (w I))
    have := h I
    simp only [natDegree_X]; omega
  have h2 : (Tens B w I).natDegree ≤ l + 1 := (natDegree_tens_le B w l h I).trans (by omega)
  have h3 : (X * Tens H w I).natDegree ≤ l + 1 := by
    refine (natDegree_mul_le).trans ?_
    have := natDegree_tens_le H w l h I
    simp only [natDegree_X]; omega
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) h3)

theorem dot_self_pos {T : Type} [Fintype T] (v : T → ℝ) (I : T) (h : v I ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_lt_of_le (mul_self_pos.mpr h)
    (Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg (v i))
      (Finset.mem_univ I))

theorem tens_zero {n r : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (I : Fin r → Fin n) :
    Tens B (fun _ => (0 : ℝ)) I = 0 := by simp [Tens]

theorem degree_core {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hH : H.IsSymm)
    (hsmall : (r : ℝ) * (sSup (spectrum ℝ B) - sInf (spectrum ℝ B)) < 1)
    (w : (Fin r → Fin n) → ℝ[X])
    (hcop : ∀ q : ℝ[X], (∀ I, q ∣ w I) → IsUnit q) (c : ℝ[X])
    (hc : ∀ I, Qop B H w I = c * w I) : ∀ I, (w I).natDegree = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨I1, hI1⟩ := hne
  set l := Finset.univ.sup (fun I => (w I).natDegree) with hl
  have hle : ∀ I, (w I).natDegree ≤ l := fun I => Finset.le_sup (f := fun I => (w I).natDegree)
    (Finset.mem_univ I)
  have hl1 : 1 ≤ l := (Nat.pos_of_ne_zero hI1).trans_le (hle I1)
  obtain ⟨Is, -, hIs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin r → Fin n))
    ⟨I1, Finset.mem_univ _⟩ (fun I => (w I).natDegree)
  have hIs' : (w Is).natDegree = l := hIs.symm
  have hwIs : w Is ≠ 0 := by
    intro h; rw [h] at hIs'; simp at hIs'; omega
  -- degree of c
  have hcdeg : c.natDegree ≤ 1 := by
    by_cases hc0 : c = 0
    · simp [hc0]
    · have h1 := natDegree_Q_le B H w l hle Is
      rw [hc Is, natDegree_mul hc0 hwIs, hIs'] at h1
      omega
  set α := c.coeff 0 with hα
  set β := c.coeff 1 with hβ
  have hcform : c = C β * X + C α := eq_X_add_C_of_natDegree_le_one hcdeg
  let wk : ℕ → (Fin r → Fin n) → ℝ := fun k I => (w I).coeff k
  have hE0 : ∀ I, Tens B (wk 0) I = α * wk 0 I := by
    intro I
    have := congrArg (fun p => p.coeff 0) (hc I)
    simp only [coeff_Q_zero] at this
    rw [this, hcform]
    simp [wk]
  have hEm : ∀ (m : ℕ) (I : Fin r → Fin n), ((m : ℝ) + 1) * wk (m + 1) I + Tens B (wk (m + 1)) I + Tens H (wk m) I =
      β * wk m I + α * wk (m + 1) I := by
    intro m I
    have := congrArg (fun p => p.coeff (m + 1)) (hc I)
    simp only [coeff_Q_succ] at this
    have hco : (c * w I).coeff (m + 1) = β * wk m I + α * wk (m + 1) I := by
      rw [hcform, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul]
    rw [this, hco]
  have hwl_ne : wk l Is ≠ 0 := by
    have : (w Is).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hwIs
    rwa [leadingCoeff, hIs'] at this
  have hw0_ne : ∃ I, wk 0 I ≠ 0 := by
    by_contra hall
    push Not at hall
    exact not_isUnit_X (hcop X fun I => X_dvd_iff.mpr (hall I))
  obtain ⟨I0, hI0⟩ := hw0_ne
  have hpos0 := dot_self_pos (wk 0) I0 hI0
  have hposl := dot_self_pos (wk l) Is hwl_ne
  -- alpha bound
  have hα1 : α * (wk 0 ⬝ᵥ wk 0) ≤ (r : ℝ) * sSup (spectrum ℝ B) * (wk 0 ⬝ᵥ wk 0) := by
    have h1 : wk 0 ⬝ᵥ Tens B (wk 0) = α * (wk 0 ⬝ᵥ wk 0) := by
      have : Tens B (wk 0) = α • wk 0 := funext hE0
      rw [this, dotProduct_smul, smul_eq_mul]
    rw [← h1]; exact top_upper B hB _
  have hα2 : α ≤ (r : ℝ) * sSup (spectrum ℝ B) := le_of_mul_le_mul_right hα1 hpos0
  -- top coefficient
  have hEtop : Tens H (wk l) = β • wk l := by
    funext I
    have := hEm l I
    have h0 : wk (l + 1) = fun _ => 0 := by
      funext J
      exact coeff_eq_zero_of_natDegree_lt (by have := hle J; omega)
    rw [h0, tens_zero] at this
    simp at this
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hvec : ((l : ℝ)) • wk l + Tens B (wk l) + Tens H (wk m) = β • wk m + α • wk l := by
    funext I
    have := hEm m I
    rw [← hm] at this
    have hl' : ((m : ℝ) + 1) = (l : ℝ) := by rw [hm]; push_cast; ring
    rw [hl'] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hdot := congrArg (fun v => wk l ⬝ᵥ v) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hdot
  rw [top_symm H hH, hEtop, smul_dotProduct, smul_eq_mul] at hdot
  rw [dotProduct_comm (wk l) (wk m)] at hdot
  have hlow := top_lower B hB (wk l)
  have key : (l : ℝ) * (wk l ⬝ᵥ wk l) ≤
      ((r : ℝ) * sSup (spectrum ℝ B) - (r : ℝ) * sInf (spectrum ℝ B)) * (wk l ⬝ᵥ wk l) := by
    nlinarith
  have key2 : (l : ℝ) ≤ (r : ℝ) * sSup (spectrum ℝ B) - (r : ℝ) * sInf (spectrum ℝ B) :=
    le_of_mul_le_mul_right key hposl
  have : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  nlinarith

end Dev.RigidityCore
end

section
set_option autoImplicit false
namespace Dev.RigidityPoly
open Polynomial

theorem ratDeriv_alg (p : ℝ[X]) :
    UniformADProbes.Trace.rationalDerivative (algebraMap ℝ[X] (RatFunc ℝ) p) =
      algebraMap ℝ[X] (RatFunc ℝ) (derivative p) := by
  unfold UniformADProbes.Trace.rationalDerivative
  simp [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

theorem gcd_split {T : Type} [Fintype T] (w0 : T → ℝ[X]) (hne : ∃ I, w0 I ≠ 0) :
    ∃ (g : ℝ[X]) (w : T → ℝ[X]), g ≠ 0 ∧ (∀ I, w0 I = g * w I) ∧
      ∀ q : ℝ[X], (∀ I, q ∣ w I) → IsUnit q := by
  classical
  set g := Finset.univ.gcd w0 with hg
  have hdvd : ∀ I, g ∣ w0 I := fun I => Finset.gcd_dvd (Finset.mem_univ I)
  choose w hw using hdvd
  have hg0 : g ≠ 0 := by
    obtain ⟨I, hI⟩ := hne
    intro h0
    have := hw I
    rw [h0, zero_mul] at this
    exact hI this
  refine ⟨g, w, hg0, hw, fun q hq => ?_⟩
  have h1 : g * q ∣ Finset.univ.gcd w0 := by
    refine Finset.dvd_gcd fun I _ => ?_
    rw [hw I]
    exact mul_dvd_mul_left g (hq I)
  have h2 : g * q ∣ g * 1 := by rw [mul_one]; exact h1
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hg0).mp h2)

theorem coprime_poly {T : Type} (w Qw : T → ℝ[X])
    (hcop : ∀ q : ℝ[X], (∀ I, q ∣ w I) → IsUnit q) (c1 : RatFunc ℝ)
    (h : ∀ I, algebraMap ℝ[X] (RatFunc ℝ) (Qw I) = c1 * algebraMap ℝ[X] (RatFunc ℝ) (w I)) :
    ∃ c : ℝ[X], ∀ I, Qw I = c * w I := by
  have hden : algebraMap ℝ[X] (RatFunc ℝ) c1.denom ≠ 0 := by
    simpa using c1.denom_ne_zero
  have hc1 : c1 = algebraMap ℝ[X] (RatFunc ℝ) c1.num / algebraMap ℝ[X] (RatFunc ℝ) c1.denom :=
    (RatFunc.num_div_denom c1).symm
  have h2 : ∀ I, c1.denom * Qw I = c1.num * w I := by
    intro I
    apply (RatFunc.algebraMap_injective ℝ).eq_iff.mp
    have hk : algebraMap ℝ[X] (RatFunc ℝ) c1.denom * c1 = algebraMap ℝ[X] (RatFunc ℝ) c1.num := by
      rw [mul_comm]; exact (eq_div_iff hden).mp hc1
    rw [map_mul, map_mul, h I, ← hk]; ring
  have hcp : IsCoprime c1.num c1.denom := RatFunc.isCoprime_num_denom c1
  have h3 : ∀ I, c1.denom ∣ w I := by
    intro I
    have : c1.denom ∣ c1.num * w I := ⟨Qw I, (h2 I).symm⟩
    exact hcp.symm.dvd_of_dvd_mul_left this
  obtain ⟨u, hu⟩ := (hcop _ h3)
  refine ⟨c1.num * ↑(u⁻¹), fun I => ?_⟩
  have : Qw I = (↑(u⁻¹) * c1.denom) * Qw I := by
    rw [← hu]; simp
  rw [this, mul_assoc, h2 I]; ring

end Dev.RigidityPoly
end

section
set_option autoImplicit false
namespace Dev.RigidityK
open Matrix Polynomial Dev.RigidityTensor Dev.RigidityId Dev.RigidityCore Dev.RigidityPoly

abbrev K := RatFunc ℝ
noncomputable abbrev φ : ℝ[X] →+* K := algebraMap ℝ[X] K

theorem trace_identity {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin r) ℝ[X])
    (Cm : Matrix (Fin r) (Fin r) K) (hC : (Dop B H F).map φ = F.map φ * Cm) (I : Fin r → Fin n) :
    φ (Qop B H (plu F) I) = φ (plu F I) * Cm.trace := by
  have h1 : Qop B H (plu F) I = ((F.submatrix I id).adjugate * ((Dop B H F).submatrix I id)).trace :=
    key_identity B H F I
  rw [h1]
  have h2 : φ (((F.submatrix I id).adjugate * ((Dop B H F).submatrix I id)).trace) =
      (((F.submatrix I id).map φ).adjugate * ((Dop B H F).submatrix I id).map φ).trace := by
    rw [AddMonoidHom.map_trace, Matrix.map_mul]
    congr 2
    exact RingHom.map_adjugate φ _
  rw [h2]
  have h3 : ((Dop B H F).submatrix I id).map φ = ((F.submatrix I id).map φ) * Cm := by
    rw [← Matrix.submatrix_map, hC]
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [h3, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, trace_smul,
    smul_eq_mul]
  unfold plu
  rw [RingHom.map_det]
  rfl

theorem scaling {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (g : ℝ[X]) (w : (Fin r → Fin n) → ℝ[X])
    (I : Fin r → Fin n) :
    Qop B H (fun J => g * w J) I = g * Qop B H w I + X * derivative g * w I := by
  have hT : ∀ M : Matrix (Fin n) (Fin n) ℝ, Tens M (fun J => g * w J) I = g * Tens M w I := by
    intro M
    simp only [Tens, Finset.mul_sum, mul_smul_comm]
  unfold Qop
  rw [hT, hT, derivative_mul]
  ring

end Dev.RigidityK
end

section
set_option autoImplicit false
namespace Dev.RigiditySetup
open Matrix Polynomial Dev.RigidityId Dev.RigidityK Dev.RigidityPoly

theorem phi_C (c : ℝ) : φ (Polynomial.C c) = algebraMap ℝ K c := by
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

theorem dop_col {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin r) ℝ[X])
    (i : Fin r) :
    (fun k => φ ((Dop B H F) k i)) =
      (RatFunc.X : K) • UniformADProbes.Trace.connection B H (fun k => φ (F k i)) := by
  funext k
  have hX : (RatFunc.X : K) ≠ 0 := RatFunc.X_ne_zero
  simp only [Dop, UniformADProbes.Trace.connection, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul,
    map_add, map_mul, map_sum, phi_C, ← RatFunc.algebraMap_X, ratDeriv_alg]
  rw [RatFunc.algebraMap_X]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have : ∀ x : Fin n, RatFunc.X * ((algebraMap ℝ (RatFunc ℝ) (B k x) / RatFunc.X +
      algebraMap ℝ (RatFunc ℝ) (H k x)) * φ (F x i)) =
      algebraMap ℝ K (B k x) * φ (F x i) + RatFunc.X * (algebraMap ℝ K (H k x) * φ (F x i)) := by
    intro x; field_simp
  simp only [this, Finset.sum_add_distrib]
  ring

theorem setup {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (V : Submodule K (Fin n → K))
    (hinv : ∀ f ∈ V, UniformADProbes.Trace.connection B H f ∈ V) :
    ∃ (F : Matrix (Fin n) (Fin (Module.finrank K V)) ℝ[X])
      (Cm : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K),
      LinearIndependent K (fun j => fun i => (F.map φ) i j) ∧
      Submodule.span K (Set.range (fun j => fun i => (F.map φ) i j)) = V ∧
      (Dop B H F).map φ = F.map φ * Cm := by
  classical
  set r := Module.finrank K V with hr
  let b : Module.Basis (Fin r) K V := Module.finBasis K V
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℝ[X])
    (fun p : Fin r × Fin n => ((b p.1 : V) : Fin n → K) p.2)
  choose p hp using fun q => hd q
  let F : Matrix (Fin n) (Fin r) ℝ[X] := Matrix.of fun k i => p (i, k)
  have hF : ∀ k i, φ (F k i) = φ (d : ℝ[X]) * ((b i : V) : Fin n → K) k := by
    intro k i
    have := hp (i, k)
    simp only [Algebra.smul_def] at this
    exact this
  have hd0 : φ (d : ℝ[X]) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    exact nonZeroDivisors.coe_ne_zero d
  have hcol : ∀ i, (fun k => (F.map φ) k i) = φ (d : ℝ[X]) • ((b i : V) : Fin n → K) := by
    intro i; funext k; simp [hF]
  have hmem : ∀ i, (fun k => (F.map φ) k i) ∈ V := by
    intro i; rw [hcol]; exact V.smul_mem _ (b i).2
  have hLI : LinearIndependent K (fun j => fun i => (F.map φ) i j) := by
    have h1 : LinearIndependent K (fun i => ((b i : V) : Fin n → K)) :=
      (b.linearIndependent).map' V.subtype (Submodule.ker_subtype V)
    have h2 := h1.map' (φ (d : ℝ[X]) • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)))
      (by
        rw [LinearMap.ker_eq_bot']
        intro m hm
        have h3 : φ (d : ℝ[X]) • m = 0 := hm
        rcases smul_eq_zero.mp h3 with h | h
        · exact absurd h hd0
        · exact h)
    have h3 : (fun j => fun i => (F.map φ) i j) =
        (φ (d : ℝ[X]) • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))) ∘
          (fun i => ((b i : V) : Fin n → K)) := by
      funext i
      exact hcol i
    rw [h3]; exact h2
  have hspan : Submodule.span K (Set.range (fun j => fun i => (F.map φ) i j)) = V := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmem j
    · intro v hv
      have hv' := b.sum_repr ⟨v, hv⟩
      have hv2 : v = ∑ i, b.repr ⟨v, hv⟩ i • ((b i : V) : Fin n → K) := by
        have := congrArg Subtype.val hv'
        rw [Submodule.coe_sum] at this
        exact this.symm
      have : v = ∑ i, (b.repr ⟨v, hv⟩ i / φ (d : ℝ[X])) •
          (fun k => (F.map φ) k i) := by
        refine hv2.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [hcol, smul_smul, div_mul_cancel₀ _ hd0]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
  have hcm : ∀ i, ∃ c : Fin r → K, (fun k => φ ((Dop B H F) k i)) =
      ∑ j, c j • (fun k => (F.map φ) k j) := by
    intro i
    rw [dop_col]
    have hm : (RatFunc.X : K) • UniformADProbes.Trace.connection B H (fun k => φ (F k i)) ∈
        Submodule.span K (Set.range (fun j => fun i => (F.map φ) i j)) := by
      rw [hspan]
      exact V.smul_mem _ (hinv _ (hmem i))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    exact ⟨c, hc.symm⟩
  choose c hc using hcm
  refine ⟨F, Matrix.of fun j i => c i j, hLI, hspan, ?_⟩
  ext k i
  have := congrFun (hc i) k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

end Dev.RigiditySetup
end

section
set_option autoImplicit false
namespace Dev.RigidityMain
open Matrix Polynomial Dev.RigidityId Dev.RigidityK Dev.RigidityPoly Dev.RigidityCore Dev.RigiditySetup

theorem const_plucker {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hH : H.IsSymm)
    (hsmall : (r : ℝ) * (sSup (spectrum ℝ B) - sInf (spectrum ℝ B)) < 1)
    (F : Matrix (Fin n) (Fin r) ℝ[X]) (Cm : Matrix (Fin r) (Fin r) K)
    (hLI : LinearIndependent K (fun j => fun i => (F.map φ) i j))
    (hC : (Dop B H F).map φ = F.map φ * Cm) :
    ∃ (g : ℝ[X]) (w0 : (Fin r → Fin n) → ℝ), g ≠ 0 ∧ (∃ I, w0 I ≠ 0) ∧
      ∀ I, plu F I = g * Polynomial.C (w0 I) := by
  obtain ⟨J0, hJ0⟩ := Dev.RigidityLA.la1 _ hLI
  have hne : ∃ I, plu F I ≠ 0 := by
    refine ⟨J0, fun h => hJ0 ?_⟩
    have : φ (plu F J0) = ((F.map φ).submatrix J0 id).det := by
      unfold plu
      rw [RingHom.map_det]
      rfl
    rw [← this, h, map_zero]
  obtain ⟨g, w, hg, hw, hcop⟩ := gcd_split (plu F) hne
  have hplu : plu F = fun I => g * w I := funext hw
  have hgK : φ g ≠ 0 := RatFunc.algebraMap_ne_zero hg
  set τ := Cm.trace
  have h1 : ∀ I, φ (Qop B H w I) = (τ - φ X * φ (derivative g) / φ g) * φ (w I) := by
    intro I
    have a1 := trace_identity B H F Cm hC I
    rw [hplu, scaling] at a1
    simp only [map_add, map_mul] at a1
    have : φ g * φ (Qop B H w I) = φ g * ((τ - φ X * φ (derivative g) / φ g) * φ (w I)) := by
      field_simp
      linear_combination a1
    exact mul_left_cancel₀ hgK this
  obtain ⟨c, hc⟩ := coprime_poly w (Qop B H w) hcop _ h1
  have hdeg := degree_core B H hB hH hsmall w hcop c hc
  have hw0 : ∀ I, w I = Polynomial.C ((w I).coeff 0) := fun I => eq_C_of_natDegree_eq_zero (hdeg I)
  refine ⟨g, fun I => (w I).coeff 0, hg, ?_, fun I => ?_⟩
  · obtain ⟨I, hI⟩ := hne
    refine ⟨I, fun h0 => hI ?_⟩
    change (w I).coeff 0 = 0 at h0
    rw [hw I, hw0 I, h0]; simp
  · rw [hw I, ← hw0 I]

end Dev.RigidityMain
end

section
set_option autoImplicit false
namespace Dev.RigidityFinal
open Matrix Polynomial Dev.RigidityId Dev.RigidityK Dev.RigiditySetup

noncomputable def coef {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) (J : Fin (r + 1) → Fin n)
    (a : Fin (r + 1)) : ℝ := (-1) ^ (a : ℕ) * w0 (J ∘ a.succAbove)

noncomputable def LK {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) (J : Fin (r + 1) → Fin n)
    (u : Fin n → K) : K := ∑ a, algebraMap ℝ K (coef w0 J a) * u (J a)

noncomputable def Lr {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) (J : Fin (r + 1) → Fin n)
    (u : Fin n → ℝ) : ℝ := ∑ a, coef w0 J a * u (J a)

theorem LK_real {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) (J : Fin (r + 1) → Fin n) (u : Fin n → ℝ) :
    LK w0 J (fun k => algebraMap ℝ K (u k)) = algebraMap ℝ K (Lr w0 J u) := by
  simp [LK, Lr, map_sum]

theorem claim1 {n r : ℕ} (F : Matrix (Fin n) (Fin r) ℝ[X])
    (hLI : LinearIndependent K (fun j => fun i => (F.map φ) i j))
    (g : ℝ[X]) (hg : g ≠ 0) (w0 : (Fin r → Fin n) → ℝ)
    (hplu : ∀ I, plu F I = g * Polynomial.C (w0 I)) (u : Fin n → K) :
    u ∈ Submodule.span K (Set.range (fun j => fun i => (F.map φ) i j)) ↔
      ∀ J, LK w0 J u = 0 := by
  rw [Dev.RigidityLA.recover _ hLI]
  have hgK : φ g ≠ 0 := RatFunc.algebraMap_ne_zero hg
  have hdet : ∀ I, ((F.map φ).submatrix I id).det = φ g * algebraMap ℝ K (w0 I) := by
    intro I
    have : φ (plu F I) = ((F.map φ).submatrix I id).det := by
      unfold plu
      rw [RingHom.map_det]
      rfl
    rw [← this, hplu, map_mul, phi_C]
  refine forall_congr' fun J => ?_
  have : ∑ a : Fin (r + 1), (-1) ^ (a : ℕ) * u (J a) * ((F.map φ).submatrix (J ∘ a.succAbove) id).det
      = φ g * LK w0 J u := by
    unfold LK coef
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hdet]; simp only [map_mul, map_pow, map_neg, map_one]; ring
  rw [this]
  simp [hgK]

/-- The real solution space of the constant linear system. -/
noncomputable def Wsub {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {u | ∀ J, Lr w0 J u = 0}
  add_mem' := by
    intro a b ha hb J
    have := ha J; have := hb J
    simp only [Lr, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    linarith
  zero_mem' := by intro J; simp [Lr]
  smul_mem' := by
    intro c a ha J
    have := ha J
    simp only [Lr, Pi.smul_apply, smul_eq_mul] at *
    rw [show ∑ x, coef w0 J x * (c * a (J x)) = c * ∑ x, coef w0 J x * a (J x) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring, this, mul_zero]

/-- the `K`-submodule of vectors killed by every `LK`. -/
noncomputable def Vc {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) : Submodule K (Fin n → K) where
  carrier := {u | ∀ J, LK w0 J u = 0}
  add_mem' := by
    intro a b ha hb J
    have h1 := ha J; have h2 := hb J
    simp only [LK, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    rw [h1, h2, add_zero]
  zero_mem' := by intro J; simp [LK]
  smul_mem' := by
    intro c a ha J
    have := ha J
    simp only [LK, Pi.smul_apply, smul_eq_mul] at *
    rw [show ∑ x, (algebraMap ℝ K) (coef w0 J x) * (c * a (J x)) =
      c * ∑ x, (algebraMap ℝ K) (coef w0 J x) * a (J x) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring, this, mul_zero]

theorem scalarExt_le {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) :
    UniformADProbes.Trace.scalarExtension (Wsub w0) ≤ Vc w0 := by
  unfold UniformADProbes.Trace.scalarExtension
  rw [Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩ J
  rw [LK_real, hu J, map_zero]

theorem le_scalarExt {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) :
    Vc w0 ≤ UniformADProbes.Trace.scalarExtension (Wsub w0) := by
  intro u hu
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℝ[X]) u
  choose p hp using fun k => hq k
  have hq0 : φ (q : ℝ[X]) ≠ 0 := RatFunc.algebraMap_ne_zero (nonZeroDivisors.coe_ne_zero q)
  have hpk : ∀ k, φ (p k) = φ (q : ℝ[X]) * u k := by
    intro k; have := hp k; simp only [Algebra.smul_def] at this; exact this
  have hpoly : ∀ J, ∑ a, Polynomial.C (coef w0 J a) * p (J a) = 0 := by
    intro J
    apply (RatFunc.algebraMap_injective ℝ).eq_iff.mp
    have h1 : φ (∑ a, Polynomial.C (coef w0 J a) * p (J a)) = φ (q : ℝ[X]) * LK w0 J u := by
      simp only [map_sum, map_mul, phi_C, hpk, LK, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, hu J]; simp
  have hW : ∀ m, (fun k => (p k).coeff m) ∈ Wsub w0 := by
    intro m J
    have := congrArg (fun f => f.coeff m) (hpoly J)
    simpa [Lr, finsetSum_coeff, coeff_C_mul] using this
  set N := Finset.univ.sup (fun k => (p k).natDegree) + 1 with hN
  have hlt : ∀ k, (p k).natDegree < N := fun k =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun k => (p k).natDegree) (Finset.mem_univ k))
  have hvec : (fun k => φ (p k)) = ∑ m ∈ Finset.range N,
      (φ Polynomial.X) ^ m • (fun k => algebraMap ℝ K ((p k).coeff m)) := by
    funext k
    rw [Finset.sum_apply]
    conv_lhs => rw [as_sum_range' (p k) N (hlt k)]
    simp only [map_sum, Pi.smul_apply, smul_eq_mul, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, phi_C, map_pow]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hmem : (fun k => φ (p k)) ∈ UniformADProbes.Trace.scalarExtension (Wsub w0) := by
    rw [hvec]
    refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, hW m, rfl⟩
  have : u = (φ (q : ℝ[X]))⁻¹ • (fun k => φ (p k)) := by
    funext k; simp [hpk, hq0]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem two_coeff (a b : ℝ) (h : algebraMap ℝ K a + RatFunc.X * algebraMap ℝ K b = 0) :
    a = 0 ∧ b = 0 := by
  have h2 : φ (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
    simp only [map_add, map_mul, phi_C, RatFunc.algebraMap_X]
    exact h
  have h3 : Polynomial.C a + Polynomial.X * Polynomial.C b = 0 :=
    (RatFunc.algebraMap_injective ℝ).eq_iff.mp (by rw [h2, map_zero])
  constructor
  · have := congrArg (fun p => p.coeff 0) h3
    simpa using this
  · have := congrArg (fun p => p.coeff 1) h3
    simpa using this

theorem LK_lin {n r : ℕ} (w0 : (Fin r → Fin n) → ℝ) (J : Fin (r + 1) → Fin n) (a b : Fin n → ℝ) :
    LK w0 J (fun k => algebraMap ℝ K (a k) + RatFunc.X * algebraMap ℝ K (b k)) =
      algebraMap ℝ K (Lr w0 J a) + RatFunc.X * algebraMap ℝ K (Lr w0 J b) := by
  simp only [LK, Lr, map_sum, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem conn_const {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (RatFunc.X : K) • UniformADProbes.Trace.connection B H (fun k => algebraMap ℝ K (u k)) =
      fun k => algebraMap ℝ K ((B.mulVec u) k) + RatFunc.X * algebraMap ℝ K ((H.mulVec u) k) := by
  funext k
  have hX : (RatFunc.X : K) ≠ 0 := RatFunc.X_ne_zero
  have hd : UniformADProbes.Trace.rationalDerivative (algebraMap ℝ K (u k)) = 0 := by
    rw [← phi_C, Dev.RigidityPoly.ratDeriv_alg]; simp
  simp only [UniformADProbes.Trace.connection, Pi.smul_apply, smul_eq_mul, hd, zero_add,
    Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

theorem final {n r : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (V : Submodule K (Fin n → K))
    (hinv : ∀ f ∈ V, UniformADProbes.Trace.connection B H f ∈ V)
    (F : Matrix (Fin n) (Fin r) ℝ[X])
    (hLI : LinearIndependent K (fun j => fun i => (F.map φ) i j))
    (hspan : Submodule.span K (Set.range (fun j => fun i => (F.map φ) i j)) = V)
    (g : ℝ[X]) (hg : g ≠ 0) (w0 : (Fin r → Fin n) → ℝ)
    (hplu : ∀ I, plu F I = g * Polynomial.C (w0 I)) :
    ∃ W : Submodule ℝ (Fin n → ℝ), V = UniformADProbes.Trace.scalarExtension W ∧
      UniformADProbes.Trace.MatrixInvariant W B ∧ UniformADProbes.Trace.MatrixInvariant W H := by
  have hV : V = Vc w0 := by
    rw [← hspan]
    ext u
    exact claim1 F hLI g hg w0 hplu u
  have hVe : V = UniformADProbes.Trace.scalarExtension (Wsub w0) :=
    hV.trans (le_antisymm (le_scalarExt w0) (scalarExt_le w0))
  refine ⟨Wsub w0, hVe, ?_, ?_⟩ <;> intro u hu J
  all_goals
    have hu' : (fun k => algebraMap ℝ K (u k)) ∈ V := by
      rw [hVe]; exact Submodule.subset_span ⟨u, hu, rfl⟩
    have h1 := hinv _ hu'
    have h2 : (RatFunc.X : K) • UniformADProbes.Trace.connection B H
        (fun k => algebraMap ℝ K (u k)) ∈ V := V.smul_mem _ h1
    rw [hV, conn_const] at h2
    have h3 := h2 J
    rw [LK_lin] at h3
    have := two_coeff _ _ h3
  · exact this.1
  · exact this.2

end Dev.RigidityFinal
end

section
set_option autoImplicit false

namespace Dev.Rigidity
open Dev.RigidityK

theorem main {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hH : H.IsSymm)
    (V : Submodule K (Fin n → K))
    (hinv : ∀ f ∈ V, UniformADProbes.Trace.connection B H f ∈ V)
    (hsmall : (Module.finrank K V : ℝ) * UniformADProbes.Trace.spectralDiameter B < 1) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      V = UniformADProbes.Trace.scalarExtension W ∧
        UniformADProbes.Trace.MatrixInvariant W B ∧ UniformADProbes.Trace.MatrixInvariant W H := by
  obtain ⟨F, Cm, hLI, hspan, hC⟩ := Dev.RigiditySetup.setup B H V hinv
  obtain ⟨g, w0, hg, -, hplu⟩ := Dev.RigidityMain.const_plucker B H hB hH hsmall F Cm hLI hC
  exact Dev.RigidityFinal.final B H V hinv F hLI hspan g hg w0 hplu

end Dev.Rigidity

namespace UniformADProbes.Trace
open Dev.Rigidity in
theorem chk_small_residue_rigidity (n : ℕ)
    (B H : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hH : H.IsSymm)
    (V : Submodule (RatFunc ℝ) (Fin n → RatFunc ℝ))
    (hinv : ∀ f ∈ V, connection B H f ∈ V)
    (hsmall : (Module.finrank (RatFunc ℝ) V : ℝ) * spectralDiameter B < 1) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      V = scalarExtension W ∧ MatrixInvariant W B ∧ MatrixInvariant W H :=
  Dev.Rigidity.main B H hB hH V hinv hsmall

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_small_residue_rigidity := @UniformADProbes.Trace.chk_small_residue_rigidity
