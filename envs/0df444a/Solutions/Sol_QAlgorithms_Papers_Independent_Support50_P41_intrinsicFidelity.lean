-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.intrinsicFidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:05:47.60348+00:00
-- url     : https://prove2.me/submissions/827d1947-2ed9-42bd-98d5-57c1c8248ae1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== P41Lib =====

noncomputable section

namespace X4P41L

open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity
  complexQuadraticForm)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {a d m : ℕ}

/-- the Kraus-branch vectors -/
def phi (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) : EuclideanSpace ℂ (Fin a × Fin d) :=
  WithLp.toLp 2 fun p => ∑ i, A k p.2 i * psi (p.1, i)

lemma idTensor_kraus (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    idTensorSuperop (krausApply A) (pureDensity psi) = ∑ k, pureDensity (phi A psi k) := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    pureDensity, conjTranspose_apply, phi, PiLp.toLp_apply, map_sum, map_mul, RCLike.star_def,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma cqf_sum {ι K : Type*} [Fintype ι] [Fintype K] (v : EuclideanSpace ℂ ι)
    (M : K → Matrix ι ι ℂ) :
    complexQuadraticForm v (∑ k, M k) = ∑ k, complexQuadraticForm v (M k) := by
  simp only [complexQuadraticForm, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]

lemma cqf_pure {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℂ ι) :
    complexQuadraticForm v (pureDensity w) = (Complex.normSq (∑ x, conj (v x) * w x) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [complexQuadraticForm, pureDensity, Matrix.of_apply, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma overlap_trace (A : Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) (B : Fin m → Matrix (Fin d) (Fin d) ℂ) (hB : B k = A) :
    ∑ x, conj (psi x) * phi B psi k x = (traceLeft (pureDensity psi) * A).trace := by
  simp only [phi, PiLp.toLp_apply, hB, Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft,
    pureDensity, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem kraus_fid (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    purificationFidelity psi (krausApply A) =
      ∑ k, Complex.normSq ((traceLeft (pureDensity psi) * A k).trace) := by
  unfold purificationFidelity
  rw [idTensor_kraus, cqf_sum]
  simp_rw [cqf_pure]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [overlap_trace (A k) psi k A rfl]

lemma choi_rel {d : ℕ} (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) :
    Phi (pureDensity v) = relativeOperator (indexState v) (choi Phi) := by
  have hv : pureDensity v = ∑ i, ∑ l, (v i * conj (v l)) • Matrix.single i l (1 : ℂ) := by
    ext x y
    simp only [pureDensity, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb, hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Ne.symm hb, hb]
    · simp
  ext j k
  rw [hv]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    relativeOperator, indexState, PiLp.toLp_apply, Complex.conj_conj, choi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end X4P41L

-- ===== P41CKLib =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41C
open Matrix

variable {d : ℕ}

/-- unnormalized maximally entangled projector on (Fin d × Fin d) -/
def omega (d : ℕ) : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma choi_psd (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    (idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))).PosSemidef :=
  hCP d _ (posSemidef_vecMulVec_self_star _)

lemma choi_entry (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (i a j b : Fin d) :
    idTensorSuperop Phi (vecMulVec (omega d) (star (omega d))) (i, a) (j, b) =
      Phi (Matrix.single i j 1) a b := by
  simp only [idTensorSuperop, Matrix.of_apply]
  have h : (Matrix.of fun x y => vecMulVec (omega d) (star (omega d)) (i, x) (j, y)) =
      Matrix.single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.of_apply, vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
    by_cases h1 : i = x <;> by_cases h2 : j = y <;> simp [h1, h2]
  rw [h]

theorem kraus_exists (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    ∃ A : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ, ∀ X, Phi X = ∑ k, A k * X * (A k)ᴴ := by
  set C := idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))
  have hC : C.PosSemidef := choi_psd Phi hCP
  set U := hC.1.eigenvectorUnitary
  set lam := hC.1.eigenvalues
  have hspec := hC.1.spectral_theorem
  have hentry : ∀ p q, C p q = ∑ k, (U : Matrix _ _ ℂ) p k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) q k) := by
    intro p q
    have := congrFun (congrFun hspec p) q
    rw [this]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, diagonal_apply, Function.comp_apply,
      star_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have hentry' : ∀ i a j b, Phi (Matrix.single i j 1) a b =
      ∑ k, (U : Matrix _ _ ℂ) (i, a) k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) (j, b) k) := by
    intro i a j b
    rw [← choi_entry Phi i a j b]
    exact hentry (i, a) (j, b)
  refine ⟨fun k => Matrix.of fun a i => ((Real.sqrt (lam k) : ℝ) : ℂ) * (U : Matrix _ _ ℂ) (i, a) k, ?_⟩
  intro X
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  ext a b
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    conjTranspose_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, Matrix.of_apply]
  simp_rw [hentry']
  simp only [Finset.mul_sum, Finset.sum_mul]
  have perm : ∀ f : Fin d → Fin d → Fin d × Fin d → ℂ,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
    intro f
    rw [Finset.sum_congr rfl (fun i _ => (Finset.sum_comm : (∑ j, ∑ k, f i j k) = _))]
    rw [(Finset.sum_comm : (∑ i, ∑ k, ∑ j, f i j k) = _)]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [perm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  have hl : 0 ≤ lam k := hC.eigenvalues_nonneg k
  have : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  linear_combination (X i j * (U : Matrix _ _ ℂ) (i, a) k * conj ((U : Matrix _ _ ℂ) (j, b) k)) * this.symm

end X4P41C

-- ===== P41IF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41I
open Matrix

variable {d a : ℕ}

lemma conj_pure {I J : Type*} [Fintype I] [Fintype J] (A : Matrix J I ℂ) (v : EuclideanSpace ℂ I) :
    A * pureDensity v * Aᴴ = pureDensity (WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v))) := by
  ext p q
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
    PiLp.toLp_apply, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

lemma phi_U {m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin a) (Fin a) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (k : Fin m) :
    X4P41L.phi A (act (Matrix.kronecker U (1 : Matrix (Fin d) (Fin d) ℂ)) psi) k =
      WithLp.toLp 2 (Matrix.kronecker U (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ
        WithLp.ofLp (X4P41L.phi A psi k)) := by
  ext ⟨r, j⟩
  simp only [X4P41L.phi, act, PiLp.toLp_apply, mulVec, dotProduct, Matrix.kronecker,
    kroneckerMap_apply, one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : ∀ s : Fin a, (∑ j1 : Fin d, ∑ x : Fin d,
      (if j = j1 then U r s * (A k j1 x * psi (s, x)) else 0)) =
      ∑ x : Fin d, U r s * (A k j x * psi (s, x)) := by
    intro s
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [Finset.sum_congr rfl fun s _ => this s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end X4P41I

theorem solution {d a b : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (phi : EuclideanSpace ℂ (Fin b × Fin d)) (hphi : IsPurification rho phi) :
    purificationFidelity psi Phi = purificationFidelity phi Phi ∧
    ∀ U : Matrix.unitaryGroup (Fin a) ℂ,
      idTensorSuperop Phi (pureDensity
        (act (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
          (1 : Matrix (Fin d) (Fin d) ℂ)) psi)) =
      conjSuperop (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
        (1 : Matrix (Fin d) (Fin d) ℂ)) (idTensorSuperop Phi (pureDensity psi)) := by
  obtain ⟨A, hA⟩ := X4P41C.kraus_exists Phi hCP
  let e : Fin d × Fin d ≃ Fin (d^2) := finProdFinEquiv.trans (finCongr (by ring))
  set A' : Fin (d^2) → Matrix (Fin d) (Fin d) ℂ := fun k => A (e.symm k)
  have hPhi : (⇑Phi : Superop (Fin d) (Fin d)) = krausApply A' := by
    funext X
    rw [hA X, krausApply]
    exact (e.symm.sum_comp (fun k => A k * X * (A k)ᴴ)).symm
  rw [hPhi]
  refine ⟨?_, fun U => ?_⟩
  · rw [X4P41L.kraus_fid, X4P41L.kraus_fid, hpsi.2, hphi.2]
  · rw [X4P41L.idTensor_kraus, X4P41L.idTensor_kraus, conjSuperop]
    simp only [X4P41I.phi_U, Matrix.mul_sum, Matrix.sum_mul, X4P41I.conj_pure]

#print axioms solution
