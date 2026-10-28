-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.stateFidelityBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:53:54.829866+00:00
-- url     : https://prove2.me/submissions/243ad704-9ada-4a28-8387-b6803a1882e7

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

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

lemma sq_sqrt (ρ : Matrix ι ι ℂ) (h : ρ.PosSemidef) : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ ρ := h.nonneg
  have := CFC.sqrt_mul_sqrt_self ρ h0
  rwa [CFC.sqrt_eq_real_sqrt ρ h0, cfcₙ_eq_cfc] at this

lemma herm_sqrt (ρ : Matrix ι ι ℂ) : (cfc Real.sqrt ρ).IsHermitian :=
  (cfc_predicate Real.sqrt ρ : IsSelfAdjoint _)

lemma cfc_trace {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma diag_of {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix ι ι ℂ) * Y * (hY.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) := by
  set U : Matrix ι ι ℂ := (hY.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  conv_lhs => rw [hY.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change star U * (U * _ * star U) * U = _
  rw [show star U * (U * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * star U) * U =
    (star U * U) * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * (star U * U) by
      simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem key (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (E : K → Matrix ι ι ℂ) :
    ∑ k, Complex.normSq ((ρ * E k).trace) ≤ rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) ^ 2 := by
  set R := cfc Real.sqrt ρ with hRdef
  have hR : Rᴴ = R := herm_sqrt ρ
  have hRR : R * R = ρ := sq_sqrt ρ hρ
  set H := R * (∑ k, E k * ρ * (E k)ᴴ) * R with hHdef
  have hHpsd : H.PosSemidef := by
    have : (∑ k, E k * ρ * (E k)ᴴ).PosSemidef :=
      Matrix.posSemidef_sum _ fun k _ => hρ.mul_mul_conjTranspose_same (E k)
    have := this.conjTranspose_mul_mul_same R
    rwa [hR] at this
  have hH : H.IsHermitian := hHpsd.1
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have hD : Uᴴ * H * U = diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]; exact diag_of hH
  have hU' : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set lam := hH.eigenvalues
  set G : K → Matrix ι ι ℂ := fun k => Uᴴ * (R * E k * R) * U
  have e : ∀ k, G k * (G k)ᴴ = Uᴴ * (R * (E k * ρ * (E k)ᴴ) * R) * U := by
    intro k
    simp only [G, Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, ← Matrix.mul_assoc R R, hRR]
  have hGG : ∑ k, G k * (G k)ᴴ = diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    rw [← hD, Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_mul, ← Matrix.mul_sum,
      ← Finset.sum_mul, ← Matrix.mul_sum, hHdef]
  have htr : ∀ k, (ρ * E k).trace = ∑ i, G k i i := by
    intro k
    change _ = (G k).trace
    rw [show G k = Uᴴ * (R * E k * R) * U from rfl, Matrix.trace_mul_cycle,
      hU', Matrix.one_mul, ← hRR, Matrix.mul_assoc, Matrix.trace_mul_comm R]
  have hrow : ∀ i, ∑ k, Complex.normSq (G k i i) ≤ lam i := by
    intro i
    have h1 := congrArg (fun M => (M i i).re) hGG
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum,
      Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj] at h1
    rw [← h1]
    refine Finset.sum_le_sum fun k _ => ?_
    exact Finset.single_le_sum (f := fun j => Complex.normSq (G k i j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hRF : rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) = ∑ i, Real.sqrt (lam i) := by
    unfold rootFidelity
    rw [← hRdef, ← hHdef, cfc_trace hH, Complex.re_sum]
    simp [lam]
  -- triangle inequality in ℓ²(K)
  let a : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 fun k => G k i i
  have hna : ∀ i, ‖a i‖ ≤ Real.sqrt (lam i) := by
    intro i
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    refine le_trans (le_of_eq ?_) (hrow i)
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [a, Complex.sq_norm]
  have hsum : ‖∑ i, a i‖ ≤ ∑ i, Real.sqrt (lam i) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hna i)
  have hlhs : ∑ k, Complex.normSq ((ρ * E k).trace) = ‖∑ i, a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [htr k, ← Complex.sq_norm]
    simp [a, WithLp.ofLp_sum]
  rw [hlhs, hRF]
  exact pow_le_pow_left₀ (norm_nonneg _) hsum 2

end X4SF

-- ===== SFBSol =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local instance (priority := 2000) instSFB (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem _root_.solution {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    purificationFidelity psi Phi ≤ rootFidelity rho (Phi rho)^2 := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  have hP : Phi = krausApply E := funext hE
  subst hP
  rw [X4P41L.kraus_fid, hpsi.2]
  exact X4SF.key rho hrho.1 E

end QAlgorithms.Papers.Independent.Support50.P41

end

#print axioms solution
