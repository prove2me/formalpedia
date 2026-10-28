-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.ensembleFidelityBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:29:49.305354+00:00
-- url     : https://prove2.me/submissions/2c7958f3-4695-46a9-bbb6-6f985a4e2b03

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

-- ===== P41PILib =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity
  complexQuadraticForm)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41P
open Matrix

variable {d : ℕ}

lemma P_sa (v : EuclideanSpace ℂ (Fin d)) : IsSelfAdjoint (pureDensity v) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose]
  ext i j
  simp [pureDensity, conjTranspose_apply, mul_comm]

lemma P_sq (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) :
    pureDensity v * pureDensity v = pureDensity v := by
  have h2 : ∑ x, conj (v x) * v x = 1 := by
    have := EuclideanSpace.norm_sq_eq v
    rw [hv, one_pow] at this
    have h : ∑ x, (‖v x‖ ^ 2 : ℝ) = (1 : ℝ) := this.symm
    have : ((∑ x, (‖v x‖ ^ 2 : ℝ) : ℝ) : ℂ) = 1 := by rw [h]; simp
    rw [← this]; push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.conj_mul']
  ext i j
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply]
  have : ∑ x, v i * conj (v x) * (v x * conj (v j)) = v i * conj (v j) * ∑ x, conj (v x) * v x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
  rw [this, h2, mul_one]

/-- functional calculus of a scaled rank-one projection -/
lemma sqrt_scaled (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) (c : ℝ) (hc : 0 ≤ c) :
    cfc Real.sqrt ((c : ℂ) • pureDensity v) = ((Real.sqrt c : ℝ) : ℂ) • pureDensity v := by
  set M := (c : ℂ) • pureDensity v
  have hsa : IsSelfAdjoint M := by
    simp only [M]
    rw [show (c : ℂ) • pureDensity v = c • pureDensity v from (Complex.coe_smul c _).symm]
    exact IsSelfAdjoint.smul (star_trivial c) (P_sa v)
  rcases hc.eq_or_lt with h | h
  · subst h; simp [M]
  have hMM : M * M = c • M := by
    simp only [M]
    rw [smul_mul_smul_comm, P_sq v hv, ← Complex.coe_smul, smul_smul]
  have hspec : ∀ x ∈ spectrum ℝ M, x = 0 ∨ x = c := by
    have e : cfc (fun x : ℝ => x ^ 2) M = cfc (fun x : ℝ => c * x) M := by
      rw [cfc_pow_id M 2 hsa, cfc_const_mul_id c M hsa, sq, hMM]
    have := eqOn_of_cfc_eq_cfc e (ha := hsa)
    intro x hx
    have := this hx
    simp only at this
    have : x * (x - c) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; exact h
    · right; linarith
  rw [cfc_congr (g := fun x => (Real.sqrt c / c) * x) (fun x hx => by
    rcases hspec x hx with rfl | rfl
    · simp
    · simp only; field_simp)]
  rw [cfc_const_mul_id _ M hsa]
  simp only [M]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

lemma P_sandwich (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) (S : Matrix (Fin d) (Fin d) ℂ) :
    pureDensity v * S * pureDensity v = complexQuadraticForm v S • pureDensity v := by
  ext i j
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    complexQuadraticForm, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma trace_P (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) : (pureDensity v).trace = 1 := by
  have := EuclideanSpace.norm_sq_eq v
  rw [hv, one_pow] at this
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  have h : ((∑ x, (‖v x‖ ^ 2 : ℝ) : ℝ) : ℂ) = 1 := by rw [← this]; simp
  rw [← h]; push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.mul_conj']

lemma trace_P_mul (v : EuclideanSpace ℂ (Fin d)) (A : Matrix (Fin d) (Fin d) ℂ) :
    (pureDensity v * A).trace = ∑ j, conj (v j) * (A *ᵥ (WithLp.ofLp v)) j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, mulVec,
    dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma conj_pure {m : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d)) :
    A * pureDensity v * Aᴴ = pureDensity (WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v))) := by
  ext p q
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
    PiLp.toLp_apply, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end X4P41P

theorem X4P41P.pure_fid {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) (hv1 : ‖v‖ = 1) :
    rootFidelity (pureDensity v) (krausApply E (pureDensity v))^2 =
      ∑ k, Complex.normSq ((pureDensity v * E k).trace) := by
  set c : ℝ := ∑ k, Complex.normSq ((pureDensity v * E k).trace)
  have hc : 0 ≤ c := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hq : complexQuadraticForm v (krausApply E (pureDensity v)) = (c : ℂ) := by
    simp only [krausApply, c]
    rw [X4P41L.cqf_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [X4P41P.conj_pure, X4P41L.cqf_pure, X4P41P.trace_P_mul]
  unfold rootFidelity
  rw [show cfc Real.sqrt (pureDensity v) = pureDensity v by
    have := X4P41P.sqrt_scaled v hv1 1 zero_le_one
    simpa using this]
  rw [X4P41P.P_sandwich v hv1, hq, X4P41P.sqrt_scaled v hv1 c hc, Matrix.trace_smul,
    X4P41P.trace_P v hv1, smul_eq_mul, mul_one, Complex.ofReal_re, Real.sq_sqrt hc]

-- ===== EF =====

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

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instEF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4EF
open Matrix

/-- countable convexity of `normSq`. -/
lemma jensen_sq {K : Type*} (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (htotal : HasSum p 1)
    (z : K → ℂ) (w : ℂ) (hw : HasSum (fun k => (p k : ℂ) * z k) w) (S : ℝ)
    (hS : HasSum (fun k => p k * Complex.normSq (z k)) S) : Complex.normSq w ≤ S := by
  have h1 : HasSum (fun k => p k * (z k * conj w).re) (Complex.normSq w) := by
    have := (Complex.hasSum_re (hw.mul_right (conj w)))
    rw [Complex.mul_conj, Complex.ofReal_re] at this
    convert this using 1
    funext k; simp [mul_assoc, Complex.mul_re]
  have h2 := (hS.add (htotal.mul_right (Complex.normSq w))).sub (h1.mul_left 2)
  have h3 : HasSum (fun k => p k * Complex.normSq (z k - w)) (S + 1 * Complex.normSq w - 2 * Complex.normSq w) := by
    have e : (fun k => p k * Complex.normSq (z k - w)) = (fun b => p b * Complex.normSq (z b) +
        p b * Complex.normSq w - 2 * (p b * (z b * (starRingEnd ℂ) w).re)) := by
      funext k; rw [Complex.normSq_sub]; ring
    rw [e]; exact h2
  have := h3.nonneg fun k => mul_nonneg (hp k) (Complex.normSq_nonneg _)
  linarith

lemma entry_bound {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) (A : Matrix (Fin d) (Fin d) ℂ) :
    Complex.normSq ((pureDensity v * A).trace) ≤ (∑ a, ∑ b, ‖A b a‖) ^ 2 := by
  have hc : ∀ a, ‖v a‖ ≤ 1 := fun a => by
    rw [← hv]; exact PiLp.norm_apply_le v a
  have hle : ‖(pureDensity v * A).trace‖ ≤ ∑ a, ∑ b, ‖A b a‖ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    have := hc a; have := hc b
    calc ‖v a‖ * ‖v b‖ * ‖A b a‖ ≤ 1 * 1 * ‖A b a‖ := by gcongr
      _ = ‖A b a‖ := by ring
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end X4EF

open X4EF in
theorem _root_.solution {K : Type*} [Countable K] {d a : ℕ} [NeZero d]
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (htotal : HasSum p 1)
    (v : K → EuclideanSpace ℂ (Fin d)) (hv : ∀ k, IsState (v k))
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (havg : HasSum (fun k => (p k : ℂ) • pureDensity (v k)) rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    Summable (fun k => p k * rootFidelity (pureDensity (v k)) (Phi (pureDensity (v k)))^2) ∧
    purificationFidelity psi Phi ≤
      ∑' k, p k * rootFidelity (pureDensity (v k)) (Phi (pureDensity (v k)))^2 := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  have hP : Phi = krausApply E := funext hE
  subst hP
  set z : K → Fin m → ℂ := fun j k => (pureDensity (v j) * E k).trace
  have hF : ∀ j, rootFidelity (pureDensity (v j)) (krausApply E (pureDensity (v j)))^2 =
      ∑ k, Complex.normSq (z j k) := fun j => X4P41P.pure_fid E (v j) (hv j)
  simp only [hF]
  -- per-Kraus summability
  have hsk : ∀ k, Summable (fun j => p j * Complex.normSq (z j k)) := by
    intro k
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hp j) (Complex.normSq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (entry_bound (v j) (hv j) (E k)) (hp j))
      (htotal.summable.mul_right _)
  have hsum : HasSum (fun j => p j * ∑ k, Complex.normSq (z j k))
      (∑ k, ∑' j, p j * Complex.normSq (z j k)) := by
    simp only [Finset.mul_sum]
    exact hasSum_sum fun k _ => (hsk k).hasSum
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, X4P41L.kraus_fid, hpsi.2]
  refine Finset.sum_le_sum fun k _ => ?_
  refine jensen_sq p hp htotal (fun j => z j k) _ ?_ _ (hsk k).hasSum
  let L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).comp
    (LinearMap.mulRight ℂ (E k))
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have := havg.map L hL
  convert this using 1
  · funext j; simp [L, z, Matrix.smul_mul, Matrix.trace_smul]
  · simp [L]

end QAlgorithms.Papers.Independent.Support50.P41

end

#print axioms solution
