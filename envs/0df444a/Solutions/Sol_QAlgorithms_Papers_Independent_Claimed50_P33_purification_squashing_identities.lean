-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.purification_squashing_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:35:41.503618+00:00
-- url     : https://prove2.me/submissions/6e25025c-4e1c-4b27-b2d3-bc11b6664517

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_stinespring_existence_uniqueness
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity

-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

end X4KF

end

-- ===== KFD =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFD (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

variable {d e : ℕ}

end X4KF

end

-- ===== KFF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix Polynomial

-- entropy swap S(VVᴴ) = S((VᴴV)ᵀ), copied from Solutions/X4/TRC.lean
variable {d m : ℕ}

end X4KF

end

-- ===== KFG =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] instKFF

namespace X4KF
open Matrix

variable {d m : ℕ}

variable {e : ℕ}

end X4KF

end

-- ===== DP =====

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

local instance (priority := 2000) instDP (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4DP
open Matrix X4KF
open scoped InnerProductSpace

variable {d e : ℕ}

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end


-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X4SU

end

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- square-root eigen-amplitudes of a PSD matrix. -/
def amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    σ = ∑ k, Matrix.of fun a b => amp hσ k a * conj (amp hσ k b) := by
  conv_lhs => rw [X4ZE.spec_sum hσ.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  have hs : ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) =
      ((hσ.1.eigenvalues k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, amp, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

end X4LE

end

-- ===== PUA =====

/-! Every extension of `ρ` is the image of a fixed purification of `ρ` under a channel on the
purifying register (via Stinespring uniqueness for the preparation map `c ↦ c ρ`). -/

noncomputable section

namespace X4PU
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33 (forgetEnvironment)
open QAlgorithms.Papers.Independent.Claimed50.P48 (stinespring_existence_uniqueness FiniteKrausCP PartialIsometry)
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

section proj
variable {S T : Type} [Fintype S] [Fintype T]

lemma one_sub_psd {P : Matrix S S ℂ} (hP : Pᴴ = P) (hPP : P * P = P) : (1 - P).PosSemidef := by
  have : 1 - P = (1 - P)ᴴ * (1 - P) := by
    rw [conjTranspose_sub, conjTranspose_one, hP, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma contr {R1 R2 : Type} [Fintype R1] [Fintype R2] (J1 : Matrix R1 S ℂ) (J2 : Matrix R2 S ℂ)
    (h1 : J1 * J1ᴴ * J1 = J1) (h2 : J2 * J2ᴴ * J2 = J2) :
    (1 - (J2 * J1ᴴ)ᴴ * (J2 * J1ᴴ)).PosSemidef := by
  have hA : (1 - J1 * J1ᴴ).PosSemidef := one_sub_psd (by simp [conjTranspose_mul]) (by
    rw [← Matrix.mul_assoc, h1])
  have hB : (1 - J2ᴴ * J2).PosSemidef := one_sub_psd (by simp [conjTranspose_mul]) (by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J2, h2])
  have e : 1 - (J2 * J1ᴴ)ᴴ * (J2 * J1ᴴ) = (1 - J1 * J1ᴴ) + J1 * (1 - J2ᴴ * J2) * J1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]; abel
  rw [e]
  exact hA.add (hB.mul_mul_conjTranspose_same J1)
end proj

lemma conj_mul_self (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma kr_entry {e : ℕ} {X R : Type} [Fintype R] (E : Matrix (Fin e) R ℂ) (u v : R → ℂ) (j j' : Fin e) :
    (E * (Matrix.of fun r r' => u r * conj (v r')) * Eᴴ) j j' =
      (∑ r, E j r * u r) * conj (∑ r, E j' r * v r) := by
  simp only [Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring

variable {X R : Type} [Fintype X] [Fintype R]

theorem ext_channel [Nonempty X] [Nonempty R] {e : ℕ} (he : 0 < e)
    (ψ : EuclideanSpace ℂ (X × R)) (hψ : ‖ψ‖ = 1)
    (σ : Matrix (X × Fin e) (X × Fin e) ℂ) (hσ : IsDensityMatrix σ)
    (hm : forgetEnvironment σ = forgetEnvironment (pureDensity ψ)) :
    ∃ Φ : Superop R (Fin e), IsChannel Φ ∧ σ = idTensorSuperop Φ (pureDensity ψ) := by
  -- purification of σ
  let Ψ : X × (Fin e × (X × Fin e)) → ℂ := fun p => X4LE.amp hσ.1 p.2.2 (p.1, p.2.1)
  have hΨ : ∀ x j y j', ∑ k, Ψ (x, (j, k)) * conj (Ψ (y, (j', k))) = σ (x, j) (y, j') := by
    intro x j y j'
    have := congrFun (congrFun (X4LE.amp_decomp hσ.1) (x, j)) (y, j')
    rw [this, Matrix.sum_apply]
    rfl
  set nR := Fintype.card R
  let eR : R ≃ Fin nR := Fintype.equivFin R
  set s2 := Fintype.card (Fin e × (X × Fin e))
  let e2 : Fin e × (X × Fin e) ≃ Fin s2 := Fintype.equivFin _
  let ρ := forgetEnvironment (pureDensity ψ)
  have hρ : ∀ x y, ρ x y = ∑ r, ψ (x, r) * conj (ψ (y, r)) := fun x y => rfl
  let Φ0 : Superop Unit X := fun c => c () () • ρ
  let W1 : Matrix (X × Fin nR) Unit ℂ := Matrix.of fun p _ => ψ (p.1, eR.symm p.2)
  let W2 : Matrix (X × Fin s2) Unit ℂ := Matrix.of fun p _ => Ψ (p.1, e2.symm p.2)
  have hW1 : receiverChannel W1 = Φ0 := by
    funext c; ext x y
    simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply,
      Fintype.univ_unit, Finset.sum_singleton, Φ0, Matrix.smul_apply, smul_eq_mul, hρ, W1]
    rw [Finset.mul_sum, ← eR.symm.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [RCLike.star_def]; ring
  have hW2 : receiverChannel W2 = Φ0 := by
    funext c; ext x y
    simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply,
      Fintype.univ_unit, Finset.sum_singleton, Φ0, Matrix.smul_apply, smul_eq_mul, W2]
    have h1 : ρ x y = ∑ j, σ (x, j) (y, j) := by
      show forgetEnvironment (pureDensity ψ) x y = _; rw [← hm]; rfl
    rw [h1, Finset.mul_sum, e2.symm.sum_comp (fun p => Ψ (x, p) * c () () * star (Ψ (y, p))),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hΨ x j y j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]; ring
  have hFK : FiniteKrausCP Φ0 := by
    refine ⟨nR, fun i => (Matrix.of fun x (_ : Unit) => ψ (x, eR.symm i) : Matrix X Unit ℂ), ?_⟩
    funext c; ext x y
    simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
      Fintype.univ_unit, Finset.sum_singleton, Φ0, Matrix.smul_apply, smul_eq_mul, hρ]
    rw [Finset.mul_sum, ← eR.symm.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [RCLike.star_def, Equiv.symm_apply_apply]; ring
  obtain ⟨r0, V0, -, -, -, huniq⟩ := stinespring_existence_uniqueness Φ0 hFK
  obtain ⟨J1, hJ1, -, hVW1⟩ := huniq nR W1 hW1
  obtain ⟨J2, hJ2, hW2V, -⟩ := huniq s2 W2 hW2
  set K := J2 * J1ᴴ with hKdef
  have hWK : W2 = ((1 : Matrix X X ℂ) ⊗ₖ K) * W1 := by
    rw [hW2V, hVW1, ← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul]
  have hKe : ∀ x t, Ψ (x, e2.symm t) = ∑ i, K t i * ψ (x, eR.symm i) := by
    intro x t
    have := congrFun (congrFun hWK (x, t)) ()
    simp only [W2, W1, Matrix.of_apply, Matrix.mul_apply, kronecker_apply, Matrix.one_apply,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul] at this
    rw [this, Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  have hQ : (1 - Kᴴ * K).PosSemidef := by convert contr J1 J2 hJ1 hJ2
  clear_value K
  set a := X4LE.amp hQ with ha_def
  have hQa := X4LE.amp_decomp hQ
  rw [← ha_def] at hQa
  -- the part of ψ outside the isometric domain of K vanishes
  have hzero : ∀ t x, ∑ i, conj (a t i) * ψ (x, eR.symm i) = 0 := by
    let U : Matrix (Fin nR) X ℂ := Matrix.of fun i x => ψ (x, eR.symm i)
    let A : Matrix (Fin nR) (Fin nR) ℂ := Matrix.of fun i t => a t i
    have hAA : A * Aᴴ = 1 - Kᴴ * K := by
      rw [hQa]; ext i i'
      simp [A, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
    have hU : (Uᴴ * U).trace = 1 := by
      have h := congrArg (fun r : ℝ => ((r ^ 2 : ℝ) : ℂ)) hψ
      simp only [EuclideanSpace.norm_eq, one_pow] at h
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)] at h
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, U, Matrix.of_apply,
        RCLike.star_def, conj_mul_self]
      push_cast at h ⊢
      rw [← h, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact eR.symm.sum_comp (fun r => ((‖ψ (x, r)‖ : ℂ) ^ 2))
    have hKU : ((K * U)ᴴ * (K * U)).trace = 1 := by
      have hKU' : ∀ t x, (K * U) t x = Ψ (x, e2.symm t) := by
        intro t x; rw [hKe]; rfl
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := (K * U)ᴴ), conjTranspose_apply, hKU']
      rw [← hσ.2]
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type (f := fun p : X × Fin e => σ p p)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [e2.symm.sum_comp (fun p => star (Ψ (x, p)) * Ψ (x, p)), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hΨ x j x j]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [RCLike.star_def]; ring
    have h0 : ((Aᴴ * U)ᴴ * (Aᴴ * U)).trace = 0 := by
      have : (Aᴴ * U)ᴴ * (Aᴴ * U) = Uᴴ * U - (K * U)ᴴ * (K * U) := by
        rw [conjTranspose_mul Aᴴ U, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc A,
          hAA, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, conjTranspose_mul K U]
        simp only [Matrix.mul_assoc]
      rw [this, Matrix.trace_sub, hU, hKU, sub_self]
    have h00 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0
    intro t x
    have := congrFun (congrFun h00 t) x
    simpa [A, U, Matrix.mul_apply, conjTranspose_apply] using this
  -- the Kraus family
  let j0 : Fin e := ⟨0, he⟩
  let F : (X × Fin e) ⊕ Fin nR → Matrix (Fin e) R ℂ := Sum.elim
    (fun k => Matrix.of fun j r => K (e2 (j, k)) (eR r))
    (fun t => Matrix.of fun j r => if j = j0 then conj (a t (eR r)) else 0)
  have hF : ∑ τ, (F τ)ᴴ * F τ = 1 := by
    rw [Fintype.sum_sum_type]
    ext r r'
    have h1 : (∑ k : X × Fin e, ((F (Sum.inl k))ᴴ * F (Sum.inl k))) r r' = (Kᴴ * K : Matrix (Fin nR) (Fin nR) ℂ) (eR r) (eR r') := by
      simp only [F, Sum.elim_inl, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
      rw [Finset.sum_comm, ← e2.sum_comp (fun t => star (K t (eR r)) * K t (eR r')), Fintype.sum_prod_type]
    have h2 : (∑ t : Fin nR, ((F (Sum.inr t))ᴴ * F (Sum.inr t))) r r' = (1 - Kᴴ * K : Matrix (Fin nR) (Fin nR) ℂ) (eR r) (eR r') := by
      rw [hQa]
      simp only [F, Sum.elim_inr, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_eq_single j0]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    rw [Matrix.add_apply, h1, h2, ← Matrix.add_apply, add_sub_cancel]
    simp [Matrix.one_apply]
  set mT := Fintype.card ((X × Fin e) ⊕ Fin nR)
  let eT : (X × Fin e) ⊕ Fin nR ≃ Fin mT := Fintype.equivFin _
  let E' : Fin mT → Matrix (Fin e) R ℂ := fun i => F (eT.symm i)
  have hE' : IsKrausFamily E' := by
    show ∑ i, (E' i)ᴴ * E' i = 1
    rw [eT.symm.sum_comp (fun τ => (F τ)ᴴ * F τ), hF]
  refine ⟨krausApply E', ⟨mT, E', hE', fun _ => rfl⟩, ?_⟩
  ext ⟨x, j⟩ ⟨y, j'⟩
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, pureDensity]
  simp only [kr_entry (X := X)]
  rw [eT.symm.sum_comp (fun τ => (∑ r, F τ j r * ψ (x, r)) * conj (∑ r, F τ j' r * ψ (y, r))),
    Fintype.sum_sum_type]
  have hl : ∀ (k : X × Fin e) (z : X) (jj : Fin e), ∑ r, F (Sum.inl k) jj r * ψ (z, r) = Ψ (z, (jj, k)) := by
    intro k z jj
    simp only [F, Sum.elim_inl, Matrix.of_apply]
    rw [← eR.symm.sum_comp, ← (Equiv.symm_apply_apply e2 (jj, k)), hKe]
    simp
  have hr : ∀ (t : Fin nR) (z : X) (jj : Fin e), ∑ r, F (Sum.inr t) jj r * ψ (z, r) = 0 := by
    intro t z jj
    simp only [F, Sum.elim_inr, Matrix.of_apply, ite_mul, zero_mul]
    split_ifs
    · rw [← eR.symm.sum_comp]; simpa using hzero t z
    · simp
  simp only [hl, hr, zero_mul, Finset.sum_const_zero, add_zero]
  exact (hΨ x j y j').symm

end X4PU

end

-- ===== LEB =====

/-! Kraus branches of a bipartite pure vector: Bob marginals, the unnormalized entanglement
functional `Gv` and its monotonicity under Alice-side Kraus families. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b : ℕ}

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

end X4ER

end

-- ===== QSQ =====

/-! Extensions of a pure multipartite state are products `ψψ† ⊗ τ`; complementary
register marginals of the pure part have equal entropy, so the total and dual
conditional informations agree on every extension. -/

noncomputable section

namespace X4QS
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P33

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

section
attribute [local instance] Classical.propDecidable Classical.decEq

end

end X4QS

end

-- ===== ERB =====

/-! Qubit erasure on one pure input with an arbitrary reference: closed forms for the output,
its marginals and their entropies. -/

noncomputable section

namespace X4EB
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {r : ℕ}

end X4EB

end

-- ===== ERC =====

/-! The dynamic score of the qubit erasure channel on an arbitrary pure ensemble:
`(1+μ)(1-ε) S(Z̄) + coeff · Σ p_x S(Z_x)`. -/

noncomputable section

namespace X4EC
open Matrix Real QAlgorithms X4EB
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

end X4EC

end

-- ===== ERD =====

noncomputable section

open Matrix Real QAlgorithms X4EB X4EC
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4ES

end X4ES


end

-- ===== ERP =====

/-! Erasure dilation (`Option A` flag): receiver/complement closed forms, flag entropy,
and concavity of von Neumann entropy for probability mixtures. -/

noncomputable section

namespace X4EP
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type} [Fintype A] [DecidableEq A]

end X4EP

end

-- ===== PEA =====

/-! Concavity of conditional entropy (both conditionings) from strong subadditivity. -/

noncomputable section

namespace X4PE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

section
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end

section
variable {M R B : Type} [Fintype M] [DecidableEq M] [Nonempty M] [Fintype R] [DecidableEq R]
  [Nonempty R] [Fintype B] [DecidableEq B] [Nonempty B]

end

end X4PE

end

-- ===== PEB =====

/-! `idTensorSuperop` of a Kraus channel: Kraus form, positivity, trace, linearity. -/

noncomputable section

namespace X4PF
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder



variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B]

/-- `1 ⊗ E`. -/
def lift1 {m : ℕ} (E : Fin m → Matrix B A ℂ) (j : Fin m) : Matrix (R × B) (R × A) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then E j p.2 q.2 else 0

@[simp] lemma lift1_apply {m : ℕ} (E : Fin m → Matrix B A ℂ) (j : Fin m) (p : R × B) (q : R × A) :
    lift1 E j p q = if p.1 = q.1 then E j p.2 q.2 else 0 := rfl

lemma idT_eq {m : ℕ} (E : Fin m → Matrix B A ℂ) (N : Superop A B) (hN : ∀ ρ, N ρ = krausApply E ρ)
    (X : Matrix (R × A) (R × A) ℂ) :
    idTensorSuperop N X = ∑ j, (lift1 (R := R) E j * X * (lift1 (R := R) E j).conjTranspose : Matrix (R × B) (R × B) ℂ) := by
  ext ⟨r, b⟩ ⟨r', b'⟩
  simp only [idTensorSuperop, hN, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    conjTranspose_apply, lift1_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single r']
  · simp [Finset.sum_mul]
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg (Ne.symm hx)]; simp
  · simp

lemma LL {m : ℕ} (E : Fin m → Matrix B A ℂ) (hE : ∑ j, (E j)ᴴ * E j = 1) :
    ∑ j, ((lift1 (R := R) E j).conjTranspose * lift1 (R := R) E j : Matrix (R × A) (R × A) ℂ) = 1 := by
  ext ⟨s, a⟩ ⟨s', a'⟩
  have h := congrFun (congrFun hE a) a'
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at h
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, lift1_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq]
  by_cases hs : s = s'
  · subst hs
    simp only [true_and]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg hb]; simp
    · simp
  · simp only [hs, false_and, if_false]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : r = s
    · subst h1; rw [if_neg hs]; simp
    · rw [if_neg h1]; simp

lemma idT_psd (N : Superop A B) (hN : IsChannel N) {X : Matrix (R × A) (R × A) ℂ} (hX : X.PosSemidef) :
    (idTensorSuperop N X).PosSemidef := by
  obtain ⟨m, E, -, hNE⟩ := hN
  rw [idT_eq E N hNE]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same _

lemma idT_trace (N : Superop A B) (hN : IsChannel N) (X : Matrix (R × A) (R × A) ℂ) :
    (idTensorSuperop N X).trace = X.trace := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  rw [idT_eq E N hNE, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm _ (lift1 (R := R) E _).conjTranspose, ← Matrix.mul_assoc, ← Matrix.trace_sum,
    ← Finset.sum_mul, LL E hE, Matrix.one_mul]

end X4PF

end

-- ===== PUSol =====

noncomputable section

namespace X4PU
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma kraus_trace {A B : Type} [Fintype A] [Fintype B] (Φ : Superop A B) (hΦ : IsChannel Φ)
    (M : Matrix A A ℂ) : (Φ M).trace = M.trace := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  rw [hΦE, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have : ∑ i, (E i)ᴴ * E i = 1 := hE
  rw [this, Matrix.one_mul]

lemma pure_psd {I : Type} [Fintype I] (ψ : EuclideanSpace ℂ I) : (pureDensity ψ).PosSemidef := by
  have : pureDensity ψ = (Matrix.of fun i (_ : Unit) => ψ i) * (Matrix.of fun i (_ : Unit) => ψ i)ᴴ := by
    ext a b; simp [pureDensity, Matrix.mul_apply, conjTranspose_apply]
  rw [this]; exact Matrix.posSemidef_self_mul_conjTranspose _

lemma pure_trace {I : Type} [Fintype I] (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    (pureDensity ψ).trace = 1 := by
  have h := congrArg (fun r : ℝ => ((r ^ 2 : ℝ) : ℂ)) hψ
  simp only [EuclideanSpace.norm_eq, one_pow] at h
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)] at h
  push_cast at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] {R : Type} [Fintype R]

lemma fe_idT {e : ℕ} (Φ : Superop R (Fin e)) (hΦ : IsChannel Φ) (ψ : EuclideanSpace ℂ (RegisterBasis D × R)) :
    forgetEnvironment (idTensorSuperop Φ (pureDensity ψ)) = forgetEnvironment (pureDensity ψ) := by
  funext a b
  have := kraus_trace Φ hΦ (Matrix.of fun i i' => pureDensity ψ (a, i) (b, i'))
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply] at this
  simp only [forgetEnvironment, idTensorSuperop, Matrix.of_apply]
  exact this

end X4PU

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexOrder Pointwise

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {m : ℕ} (hm : 2 ≤ m)
    {D : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {R : Type} [Fintype R] [Nonempty R]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (RegisterBasis D × R)) (hpsi : ‖psi‖ = 1)
    (hmarginal : forgetEnvironment (pureDensity psi) = rho) :
    (∀ e : ℕ, 0 < e → ∀ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma → forgetEnvironment sigma = rho →
      ∃ Phi : Superop R (Fin e), IsChannel Phi ∧
        sigma = idTensorSuperop Phi (pureDensity psi)) ∧
    (halfExtensionSquashed .total rho = halfChannelSquashed .total psi) ∧
    (halfExtensionSquashed .dual rho = halfChannelSquashed .dual psi) := by
  have part1 : ∀ e : ℕ, 0 < e → ∀ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
      IsDensityMatrix sigma → forgetEnvironment sigma = rho →
      ∃ Phi : Superop R (Fin e), IsChannel Phi ∧ sigma = idTensorSuperop Phi (pureDensity psi) :=
    fun e he sigma hs hf => X4PU.ext_channel he psi hpsi sigma hs (by rw [hf, hmarginal])
  have key : ∀ kind : InformationKind, halfExtensionSquashed kind rho = halfChannelSquashed kind psi := by
    intro kind
    simp only [halfExtensionSquashed, halfChannelSquashed, multipartiteSquashed]
    set S := {v : ℝ | ∃ e : ℕ, 0 < e ∧
      ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
        IsDensityMatrix sigma ∧ forgetEnvironment sigma = rho ∧
        (false = true → IsClassicalExtension sigma) ∧
        v = conditionalMultipartiteInformation kind sigma (singleParties m) ∅}
    have hT : {v : ℝ | ∃ e : ℕ, 0 < e ∧ ∃ Phi : Superop R (Fin e),
        IsChannel Phi ∧ v = conditionalMultipartiteInformation kind
          (idTensorSuperop Phi (pureDensity psi)) (singleParties m) ∅ / 2} = (2⁻¹ : ℝ) • S := by
      ext v
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨e, he, Phi, hPhi, rfl⟩
        refine ⟨_, ⟨e, he, idTensorSuperop Phi (pureDensity psi),
          ⟨X4PF.idT_psd Phi hPhi (X4PU.pure_psd psi), by
            rw [X4PF.idT_trace Phi hPhi, X4PU.pure_trace psi hpsi]⟩,
          by rw [X4PU.fe_idT Phi hPhi, hmarginal], fun h => absurd h (by decide), rfl⟩, ?_⟩
        simp only [smul_eq_mul]; ring
      · rintro ⟨w, ⟨e, he, sigma, hs, hf, -, rfl⟩, rfl⟩
        obtain ⟨Phi, hPhi, rfl⟩ := part1 e he sigma hs hf
        exact ⟨e, he, Phi, hPhi, by simp only [smul_eq_mul]; ring⟩
    rw [hT, Real.sInf_smul_of_nonneg (by norm_num), smul_eq_mul]
    ring
  exact ⟨part1, key .total, key .dual⟩

