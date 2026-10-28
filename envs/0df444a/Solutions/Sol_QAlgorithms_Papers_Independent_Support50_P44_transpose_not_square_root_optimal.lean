-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.transpose_not_square_root_optimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:08:40.763637+00:00
-- url     : https://prove2.me/submissions/9dfdf950-d432-4528-8251-4c12ea56e9ea

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section
open scoped Matrix

namespace X7cr

variable {I : Type} [Fintype I] [DecidableEq I]

lemma conj_herm (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) :
    IsSelfAdjoint ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) := by
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; funext i; simp
  exact Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix I I ℂ) hD

lemma spec_sub (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) (x : ℝ)
    (hx : x ∈ spectrum ℝ ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ)) :
    ∃ i, d i = x := by
  have e : ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) =
      Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U (Matrix.diagonal (fun i => (d i : ℂ))) := rfl
  rw [e, AlgEquiv.spectrum_eq] at hx
  have h2 : algebraMap ℝ ℂ x ∈ spectrum ℂ (Matrix.diagonal (fun i => (d i : ℂ))) :=
    (spectrum.algebraMap_mem_iff ℂ).mpr hx
  rw [spectrum_diagonal] at h2
  obtain ⟨i, hi⟩ := h2
  exact ⟨i, by simpa using hi⟩

lemma cfc_conj (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) =
      (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (f (d i) : ℂ)) * (U : Matrix I I ℂ)ᴴ := by
  set M := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ
  have hM : IsSelfAdjoint M := conj_herm U d
  let s : Finset ℝ := Finset.univ.image d
  let P : Polynomial ℝ := Lagrange.interpolate s id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _)
      (Finset.mem_image_of_mem d (Finset.mem_univ i))
    simpa [P] using this
  have h1 : cfc f M = cfc (fun x => P.eval x) M := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := spec_sub U d x hx
    exact (hP i).symm
  rw [h1, cfc_polynomial P M hM]
  have e : M = Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U (Matrix.diagonal (fun i => (d i : ℂ))) := rfl
  rw [e, Polynomial.aeval_algHom_apply, Unitary.conjStarAlgAut_apply]
  congr 2
  have : Matrix.diagonal (fun i => (d i : ℂ)) = Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) := rfl
  rw [this, Polynomial.aeval_algHom_apply]
  simp only [Matrix.diagonalAlgHom_apply]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply]   -- may need adjusting
  rw [← hP i]
  have := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (d i) P
  simpa using this

end X7cr

end


noncomputable section
open scoped Matrix ComplexOrder

namespace X7tn
open QAlgorithms

lemma cfc_diag {I : Type} [Fintype I] [DecidableEq I] (d : I → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  have := X7cr.cfc_conj (1 : Matrix.unitaryGroup I ℂ) d f
  simpa using this

lemma rootFid_diag {I : Type} [Fintype I] [DecidableEq I] (p q : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    rootFidelity (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ))) =
      ∑ i, Real.sqrt (p i * q i) := by
  unfold rootFidelity
  rw [cfc_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have : (fun i => ((Real.sqrt (p i) : ℂ) * (q i : ℂ) * (Real.sqrt (p i) : ℂ))) =
      fun i => ((p i * q i : ℝ) : ℂ) := by
    funext i
    have h := Real.mul_self_sqrt (hp i)
    have : ((Real.sqrt (p i) : ℂ) * (q i : ℂ) * (Real.sqrt (p i) : ℂ)) =
        ((Real.sqrt (p i) * Real.sqrt (p i) * q i : ℝ) : ℂ) := by push_cast; ring
    rw [this, h]
  rw [this, cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma kraus_idTensor {R ι κ K : Type} [Fintype R] [DecidableEq R] [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (X : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (R := R) (krausApply E) X =
      ∑ j, Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j) * X * (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))ᴴ := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single q.1 (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp only [if_true]
  congr 1
  rw [Finset.sum_eq_single p.1 (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp

lemma kraus_idTensor_psd {R ι κ K : Type} [Fintype R] [DecidableEq R] [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (X : Matrix (R × ι) (R × ι) ℂ) (hX : X.PosSemidef) :
    (idTensorSuperop (R := R) (krausApply E) X).PosSemidef := by
  rw [kraus_idTensor]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same _

lemma kraus_idTensor_tr {R ι κ K : Type} [Fintype R] [DecidableEq R] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) (X : Matrix (R × ι) (R × ι) ℂ) :
    (idTensorSuperop (R := R) (krausApply E) X).trace = X.trace := by
  rw [kraus_idTensor, Matrix.trace_sum]
  have : ∀ j, (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j) * X *
      (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))ᴴ).trace =
      (X * ((Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))ᴴ * Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))).trace := by
    intro j; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [this, ← Matrix.trace_sum, ← Matrix.mul_sum]
  have hs : ∑ j, (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))ᴴ * Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j) =
      Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (∑ j, (E j)ᴴ * E j) := by
    have e : ∀ j, (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j))ᴴ * Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (E j) =
        Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) ((E j)ᴴ * E j) := by
      intro j
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul]
    simp only [e]
    ext a b
    simp [Matrix.sum_apply, Finset.mul_sum]
  rw [hs, hE, Matrix.one_kronecker_one, Matrix.mul_one]

lemma sqrt_le_half (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ (1 + x) / 2 := by
  nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 1)]

lemma tr_sqrt_le {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (hM : M.PosSemidef) :
    (cfc Real.sqrt M).trace.re ≤ (Fintype.card I + M.trace.re) / 2 := by
  have hH := hM.1
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal,
    hH.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Function.comp_apply, Complex.ofReal_re, RCLike.ofReal_re]
  have : ∑ i, Real.sqrt (hH.eigenvalues i) ≤ ∑ i, (1 + hH.eigenvalues i) / 2 :=
    Finset.sum_le_sum fun i _ => sqrt_le_half _ (hM.eigenvalues_nonneg i)
  rw [← Finset.sum_div, Finset.sum_add_distrib] at this
  simpa using this

end X7tn

end


noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate

namespace X7tn
open QAlgorithms

lemma chan_of_kraus {K ι κ : Type} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) (Φ : Superop ι κ) (h : ∀ ρ, Φ ρ = krausApply E ρ) :
    IsChannel Φ := by
  refine ⟨Fintype.card K, fun k => E ((Fintype.equivFin K).symm k), ?_, ?_⟩
  · unfold IsKrausFamily at hE ⊢
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun j => (E j)ᴴ * E j)
  · intro ρ
    rw [h ρ]
    unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun j => E j * ρ * (E j)ᴴ)).symm

/-- Kraus operators of a "sandwich" map X ↦ s (d X d ⊗ 1) s. -/
def sandK {B C : Type} [DecidableEq B] [DecidableEq C] (s : B × C → ℝ) (d : B → ℝ) (c : C) :
    Matrix (B × C) B ℂ :=
  fun i b => if i.1 = b ∧ i.2 = c then ((s i * d b : ℝ) : ℂ) else 0

lemma sandK_apply {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (s : B × C → ℝ) (d : B → ℝ) (X : Matrix B B ℂ) (i j : B × C) :
    krausApply (sandK s d) X i j =
      if i.2 = j.2 then ((s i * d i.1 : ℝ) : ℂ) * X i.1 j.1 * ((s j * d j.1 : ℝ) : ℂ) else 0 := by
  unfold krausApply
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single i.2]
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sandK]
    rw [Finset.sum_eq_single j.1]
    · rw [Finset.sum_eq_single i.1]
      · by_cases h : i.2 = j.2
        · simp [h, Complex.conj_ofReal]
        · simp [h, Ne.symm h]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro c _ hc
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sandK]
    apply Finset.sum_eq_zero; intro b _
    simp [Ne.symm hc]
  · simp

lemma sandK_kraus {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (s : B × C → ℝ) (d : B → ℝ) (h : ∀ b, ∑ c, (s (b, c) * d b) ^ 2 = 1) :
    IsKrausFamily (sandK s d) := by
  unfold IsKrausFamily
  ext x y
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sandK, Fintype.sum_prod_type,
    Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, show (1:ℂ) = ((1:ℝ):ℂ) by simp, ← h x]
    push_cast
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.sum_eq_single x (by intro b _ hb; simp [hb]) (by simp)]
    rw [Finset.sum_eq_single c (by intro b _ hb; simp [hb]) (by simp)]
    simp [Complex.conj_ofReal]; ring
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c' _
    by_cases h1 : b = x
    · subst h1; simp [hxy]
    · simp [h1]

end X7tn

end


noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate

namespace X7tn
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev T3 := Bool × (Bool × Bool)

def rv (z : T3) : ℝ := if z.1 then 1/8 else if z.2 = (false, false) then 1/2 else 0
def abv (z : Bool × Bool) : ℝ := if z.1 then 1/4 else if z.2 then 0 else 1/2
def bcv (z : Bool × Bool) : ℝ := if z = (false, false) then 5/8 else 1/8
def rbv (b : Bool) : ℝ := if b then 1/4 else 3/4

lemma st_eq : counterexampleState = Matrix.diagonal (fun z => (rv z : ℂ)) := by
  unfold counterexampleState rv
  congr 1; funext z; split_ifs <;> simp

lemma ab_eq : marginalAB counterexampleState = Matrix.diagonal (fun z => (abv z : ℂ)) := by
  rw [st_eq]
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [marginalAB, Matrix.diagonal_apply, Fintype.sum_bool, Prod.mk.injEq, abv, rv]
  cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num

lemma bc_eq : traceLeft counterexampleState = Matrix.diagonal (fun z => (bcv z : ℂ)) := by
  rw [st_eq]
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [traceLeft, Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_bool, Prod.mk.injEq, bcv, rv]
  cases a <;> cases b <;> cases a' <;> cases b' <;> norm_num

lemma rb_eq : (fun b b2 => ∑ c, (traceLeft counterexampleState) (b, c) (b2, c) : Matrix Bool Bool ℂ) =
    Matrix.diagonal (fun b => (rbv b : ℂ)) := by
  rw [bc_eq]
  ext b b'
  cases b <;> cases b' <;> simp [Matrix.diagonal_apply, Fintype.sum_bool, bcv, rbv] <;> norm_num

lemma bcv_nn (z : Bool × Bool) : 0 ≤ bcv z := by unfold bcv; split_ifs <;> norm_num
lemma rbv_nn (b : Bool) : 0 ≤ rbv b := by unfold rbv; split_ifs <;> norm_num

def sv (z : Bool × Bool) : ℝ := Real.sqrt (bcv z)
def dv (b : Bool) : ℝ := (Real.sqrt (rbv b))⁻¹

lemma tr_formula (X : Matrix Bool Bool ℂ) :
    counterexampleTranspose X = krausApply (sandK sv dv) X := by
  ext i j
  rw [sandK_apply]
  unfold counterexampleTranspose rotatedTranspose
  rw [rb_eq, bc_eq, cfc_diag, cfc_diag]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply]
  by_cases h : i.2 = j.2
  · rw [if_pos h, if_pos h]; simp only [sv, dv]; push_cast; ring
  · rw [if_neg h, if_neg h]; simp

lemma sandK_tp : IsKrausFamily (sandK sv dv) := by
  apply sandK_kraus
  intro b
  simp only [Fintype.sum_bool, sv, dv, mul_pow, inv_pow]
  rw [Real.sq_sqrt (bcv_nn _), Real.sq_sqrt (bcv_nn _), Real.sq_sqrt (rbv_nn _)]
  cases b <;> norm_num [bcv, rbv]

lemma T_chan : IsChannel counterexampleTranspose :=
  chan_of_kraus _ sandK_tp _ tr_formula

end X7tn

end


noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate

namespace X7tn
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma sd_sq (z : Bool × Bool) : (sv z * dv z.1) ^ 2 = bcv z / rbv z.1 := by
  simp only [sv, dv, mul_pow, inv_pow, Real.sq_sqrt (bcv_nn _), Real.sq_sqrt (rbv_nn _)]
  ring

def srv (z : T3) : ℝ := if z.2 = (false, false) then abv (z.1, false) else 1/3 * abv (z.1, true)
def stv (z : T3) : ℝ := bcv z.2 / rbv z.2.1 * abv (z.1, z.2.1)

lemma sR_eq : idTensorSuperop counterexampleRecovery (marginalAB counterexampleState) =
    Matrix.diagonal (fun z => (srv z : ℂ)) := by
  rw [ab_eq]
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  simp only [idTensorSuperop, counterexampleRecovery, Matrix.of_apply, Matrix.diagonal_apply, srv, abv,
    Prod.mk.injEq]
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> norm_num

lemma sT_eq : idTensorSuperop counterexampleTranspose (marginalAB counterexampleState) =
    Matrix.diagonal (fun z => (stv z : ℂ)) := by
  have hT : counterexampleTranspose = krausApply (sandK sv dv) := funext tr_formula
  rw [hT, ab_eq]
  ext p q
  simp only [idTensorSuperop, Matrix.of_apply]
  rw [sandK_apply]
  simp only [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, Matrix.of_apply]
    have h := sd_sq p.2
    have e : ((sv p.2 * dv p.2.1 : ℝ) : ℂ) * ((abv (p.1, p.2.1) : ℝ) : ℂ) * ((sv p.2 * dv p.2.1 : ℝ) : ℂ) =
        (((sv p.2 * dv p.2.1) ^ 2 * abv (p.1, p.2.1) : ℝ) : ℂ) := by push_cast; ring
    rw [e, h]; rfl
  · rw [if_neg hpq]
    simp only [Matrix.of_apply]
    by_cases h1 : p.2.2 = q.2.2
    · by_cases h2 : (p.1, p.2.1) = (q.1, q.2.1)
      · exfalso; apply hpq
        rcases p with ⟨a, b, c⟩; rcases q with ⟨a', b', c'⟩
        simp only [Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨h2.1, h2.2, h1⟩
      · simp [h1, h2]
    · simp [h1]

lemma s3a : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
lemma s3b : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = 1/3 := by
  rw [← mul_inv, ← sq, s3a]; norm_num

def RK (z : Bool × Bool) : Matrix (Bool × Bool) Bool ℂ := fun w b =>
  if w = z then (if z = (false, false) then (if b = false then 1 else 0)
    else (if b = true then ((Real.sqrt (1/3) : ℝ) : ℂ) else 0)) else 0

lemma s3 : ((Real.sqrt (1/3) : ℝ) : ℂ) * ((Real.sqrt (1/3) : ℝ) : ℂ) = 1/3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma RK_kraus : IsKrausFamily RK := by
  unfold IsKrausFamily
  ext b b'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RK, Fintype.sum_prod_type,
    Fintype.sum_bool, Matrix.one_apply]
  cases b <;> cases b' <;> simp [Complex.conj_ofReal, s3] <;> (try rw [s3b]) <;> norm_num

lemma RK_apply (X : Matrix Bool Bool ℂ) : counterexampleRecovery X = krausApply RK X := by
  ext ⟨b, c⟩ ⟨b', c'⟩
  simp only [counterexampleRecovery, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RK, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.diagonal_apply]
  cases b <;> cases c <;> cases b' <;> cases c' <;> simp [Complex.conj_ofReal] <;> (try linear_combination (-(X true true)) * s3b)

lemma R_chan : IsChannel counterexampleRecovery := chan_of_kraus _ RK_kraus _ RK_apply

end X7tn

end


noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate

namespace X7tn
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma rv_nn (z : T3) : 0 ≤ rv z := by unfold rv; split_ifs <;> norm_num

lemma FR_val : rootFidelity counterexampleState
    (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) =
    1/2 + Real.sqrt (1/32) + 3 * Real.sqrt (1/96) := by
  rw [sR_eq, st_eq, rootFid_diag _ _ rv_nn]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, rv, srv, abv]
  norm_num
  ring

lemma FT_val : rootFidelity counterexampleState
    (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState)) =
    Real.sqrt (5/24) + Real.sqrt (5/192) + Real.sqrt (1/192) + 1/4 := by
  rw [sT_eq, st_eq, rootFid_diag _ _ rv_nn]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, rv, stv, abv, bcv, rbv]
  norm_num
  ring

lemma FR_gt : 9829/10000 < rootFidelity counterexampleState
    (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) := by
  rw [FR_val]
  have h1 : (17677/100000 : ℝ) < Real.sqrt (1/32) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : (10206/100000 : ℝ) < Real.sqrt (1/96) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

lemma FT_lt : Real.sqrt (rootFidelity counterexampleState
    (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState))) < 9696/10000 := by
  rw [FT_val, Real.sqrt_lt' (by norm_num)]
  have h1 : Real.sqrt (5/24) < 45644/100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : Real.sqrt (5/192) < 16138/100000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : Real.sqrt (1/192) < 72169/1000000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  nlinarith

end X7tn

end


noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate

namespace X7tn
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma st_dens : IsDensityMatrix counterexampleState := by
  rw [st_eq]
  refine ⟨Matrix.PosSemidef.diagonal (fun z => ?_), ?_⟩
  · simp only [Pi.zero_apply]; exact_mod_cast rv_nn z
  · rw [Matrix.trace_diagonal]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, rv]
    norm_num

lemma ab_psd : (marginalAB counterexampleState).PosSemidef := by
  rw [ab_eq]
  refine Matrix.PosSemidef.diagonal (fun z => ?_)
  simp only [Pi.zero_apply]
  have : 0 ≤ abv z := by unfold abv; split_ifs <;> norm_num
  exact_mod_cast this

lemma ab_tr : (marginalAB counterexampleState).trace = 1 := by
  rw [ab_eq, Matrix.trace_diagonal]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, abv]
  norm_num

lemma T_single (b : Bool) (i j : Bool × Bool) :
    counterexampleTranspose (Matrix.single b b 1) i j =
      if i = j ∧ i.1 = b then ((bcv i / rbv i.1 : ℝ) : ℂ) else 0 := by
  rw [tr_formula, sandK_apply]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, true_and, Matrix.single_apply]
    by_cases hb : i.1 = b
    · rw [if_pos ⟨hb.symm, hb.symm⟩, if_pos hb, ← sd_sq]; push_cast; ring
    · rw [if_neg (fun h => hb h.1.symm), if_neg hb]; simp
  · have hr : ¬(i = j ∧ i.1 = b) := fun h => hij h.1
    rw [if_neg hr]
    by_cases h : i.2 = j.2
    · have hs : ¬(b = i.1 ∧ b = j.1) := fun h' => hij (Prod.ext (h'.1.symm.trans h'.2) h)
      rw [if_pos h, Matrix.single_apply, if_neg hs]; simp
    · rw [if_neg h]

lemma T0 : counterexampleTranspose (Matrix.single false false 1) =
      Matrix.diagonal (fun z => if z = (false,false) then (5/6 : ℂ)
        else if z = (false,true) then (1/6 : ℂ) else 0) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rw [T_single, Matrix.diagonal_apply]
  cases x <;> cases y <;> cases x' <;> cases y' <;> norm_num [bcv, rbv]

lemma T1 : counterexampleTranspose (Matrix.single true true 1) =
      Matrix.diagonal (fun z => if z.1 then (1/2 : ℂ) else 0) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rw [T_single, Matrix.diagonal_apply]
  cases x <;> cases y <;> cases x' <;> cases y' <;> norm_num [bcv, rbv]

lemma fid_bound (R : {R : Superop Bool (Bool × Bool) // IsChannel R}) :
    rootFidelity counterexampleState (idTensorSuperop R.val (marginalAB counterexampleState)) ≤ 9/2 := by
  obtain ⟨m, E, hE, hR⟩ := R.2
  have hRe : R.val = krausApply E := funext hR
  set σ := idTensorSuperop R.val (marginalAB counterexampleState) with hσ
  have hpsd : σ.PosSemidef := by rw [hσ, hRe]; exact kraus_idTensor_psd E _ ab_psd
  have htr : σ.trace = 1 := by rw [hσ, hRe, kraus_idTensor_tr E hE, ab_tr]
  unfold rootFidelity
  rw [st_eq, cfc_diag]
  set D : Matrix T3 T3 ℂ := Matrix.diagonal (fun z => ((Real.sqrt (rv z) : ℝ) : ℂ)) with hD
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]; congr 1; funext z; simp
  have hM : (D * σ * D).PosSemidef := by
    have := hpsd.mul_mul_conjTranspose_same D
    rwa [hDh] at this
  have h1 := tr_sqrt_le _ hM
  have hcard : (Fintype.card T3 : ℝ) = 8 := by simp
  have h2 : (D * σ * D).trace.re ≤ 1 := by
    have e : ∀ z, (D * σ * D) z z = ((rv z : ℝ) : ℂ) * σ z z := by
      intro z
      rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
      have := Real.mul_self_sqrt (rv_nn z)
      calc ((Real.sqrt (rv z) : ℝ) : ℂ) * σ z z * ((Real.sqrt (rv z) : ℝ) : ℂ)
          = ((Real.sqrt (rv z) * Real.sqrt (rv z) : ℝ) : ℂ) * σ z z := by push_cast; ring
        _ = _ := by rw [this]
    have htr' : σ.trace.re = 1 := by rw [htr]; simp
    rw [Matrix.trace, Complex.re_sum]
    rw [Matrix.trace, Complex.re_sum] at htr'
    rw [← htr']
    apply Finset.sum_le_sum
    intro z _
    simp only [Matrix.diag_apply, e, Complex.re_ofReal_mul]
    have hσz : 0 ≤ (σ z z).re := (Complex.nonneg_iff.mp (hpsd.diag_nonneg)).1
    have hr : rv z ≤ 1 := by unfold rv; split_ifs <;> norm_num
    nlinarith [rv_nn z]
  rw [hcard] at h1
  linarith

end X7tn

end

section
namespace QAlgorithms.Papers.Independent.Support50.P44
end QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P44
open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)
open Filter
open scoped ENNReal ComplexOrder Matrix
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem solution :
    IsDensityMatrix counterexampleState ∧ IsChannel counterexampleRecovery ∧
    IsChannel counterexampleTranspose ∧
    counterexampleTranspose (Matrix.single false false 1) =
      Matrix.diagonal (fun z => if z = (false,false) then (5/6 : ℂ)
        else if z = (false,true) then (1/6 : ℂ) else 0) ∧
    counterexampleTranspose (Matrix.single true true 1) =
      Matrix.diagonal (fun z => if z.1 then (1/2 : ℂ) else 0) ∧
    9829/10000 < rootFidelity counterexampleState
      (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) ∧
    Real.sqrt (rootFidelity counterexampleState
      (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState))) < 9696/10000 ∧
    rootFidelity counterexampleState
      (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) ≤
        finiteRecoveryFidelity counterexampleState ∧
    Real.sqrt (rootFidelity counterexampleState
      (idTensorSuperop counterexampleTranspose (marginalAB counterexampleState))) <
        finiteRecoveryFidelity counterexampleState := by
  have hle : rootFidelity counterexampleState
      (idTensorSuperop counterexampleRecovery (marginalAB counterexampleState)) ≤
        finiteRecoveryFidelity counterexampleState := by
    unfold finiteRecoveryFidelity
    refine le_ciSup (f := fun R : {R : Superop Bool (Bool × Bool) // IsChannel R} =>
      rootFidelity counterexampleState (idTensorSuperop R.val (marginalAB counterexampleState)))
      ⟨9/2, ?_⟩ ⟨counterexampleRecovery, X7tn.R_chan⟩
    rintro _ ⟨R, rfl⟩
    exact X7tn.fid_bound R
  refine ⟨X7tn.st_dens, X7tn.R_chan, X7tn.T_chan, X7tn.T0, X7tn.T1, X7tn.FR_gt, X7tn.FT_lt, hle, ?_⟩
  have := X7tn.FR_gt
  have := X7tn.FT_lt
  linarith

end
