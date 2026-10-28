-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.relativeFiniteBlock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:01:19.735993+00:00
-- url     : https://prove2.me/submissions/3ae3451d-f3d5-472b-b878-9ecf04a1eee9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_fixedReferenceFiniteBlock

section X5mod_RB_Base
open Matrix
open scoped ComplexOrder

namespace X5RB
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

section
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

noncomputable def rx (e : m ≃ n) : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
    map_star' := fun X => by
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex] }

lemma rx_apply (e : m ≃ n) (X : Matrix m m ℂ) : rx e X = reindex e e X := rfl

lemma rmul (e : m ≃ n) (X Y : Matrix m m ℂ) : reindex e e X * reindex e e Y = reindex e e (X * Y) := by
  rw [← rx_apply, ← rx_apply, ← rx_apply, map_mul]

lemma tr_rx (e : m ≃ n) (X : Matrix m m ℂ) : (reindex e e X).trace = X.trace := by
  simp only [Matrix.trace, diag_apply, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => X i i)

lemma sa_rx (e : m ≃ n) (X : Matrix m m ℂ) : IsSelfAdjoint (reindex e e X) ↔ IsSelfAdjoint X := by
  constructor
  · intro h
    have : reindex e.symm e.symm (reindex e e X) = X := by ext; simp [reindex_apply]
    rw [← this]
    have h' : (reindex e.symm e.symm (reindex e e X))ᴴ = reindex e.symm e.symm (reindex e e X) := by
      rw [Matrix.conjTranspose_reindex]; exact congrArg _ h
    exact h'
  · intro h
    have h' : (reindex e e X)ᴴ = reindex e e X := by rw [Matrix.conjTranspose_reindex]; exact congrArg _ h
    exact h'

lemma cfc_rx (e : m ≃ n) (X : Matrix m m ℂ) (f : ℝ → ℝ) :
    cfc f (reindex e e X) = reindex e e (cfc f X) := by
  by_cases hX : IsSelfAdjoint X
  · have hc : Continuous (rx e) := by
      change Continuous fun X : Matrix m m ℂ => reindex e e X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [reindex_apply, submatrix_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (rx e) f X (X.finite_real_spectrum.continuousOn _) hc hX ((sa_rx e X).2 hX)
    exact h.symm
  · rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate _ (fun h => hX ((sa_rx e X).1 h))]
    ext; simp [reindex_apply]

lemma psd_rx (e : m ≃ n) (X : Matrix m m ℂ) : (reindex e e X).PosSemidef ↔ X.PosSemidef := by
  rw [reindex_apply]; exact posSemidef_submatrix_equiv e.symm

lemma rootFidelity_rx (e : m ≃ n) (X Y : Matrix m m ℂ) :
    rootFidelity (reindex e e X) (reindex e e Y) = rootFidelity X Y := by
  unfold rootFidelity
  rw [cfc_rx, rmul, rmul, cfc_rx, tr_rx]

lemma sub_rx (e : m ≃ n) (X : Matrix m m ℂ) (Y : Matrix m m ℂ) (c : ℂ) :
    c • reindex e e X - reindex e e Y = reindex e e (c • X - Y) := by
  ext; simp [reindex_apply]

lemma supp_rx (e : m ≃ n) (X Y : Matrix m m ℂ) :
    supportedBy (reindex e e X) (reindex e e Y) ↔ supportedBy X Y := by
  have key : ∀ (M : Matrix m m ℂ) (v : n → ℂ), reindex e e M *ᵥ v = (M *ᵥ (v ∘ e)) ∘ e.symm := by
    intro M v; ext i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Function.comp_apply]
    exact (Equiv.sum_comp e.symm (fun j => M (e.symm i) j * v (e j))).symm.trans (by simp) |>.symm
  have key0 : ∀ (M : Matrix m m ℂ) (v : n → ℂ), reindex e e M *ᵥ v = 0 ↔ M *ᵥ (v ∘ e) = 0 := by
    intro M v; rw [key]; constructor
    · intro h; ext j; have := congrFun h (e j); simpa using this
    · intro h; rw [h]; rfl
  unfold supportedBy
  constructor
  · intro h x hx
    rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
    have h1 : x ∘ e.symm ∘ e = x := by ext; simp
    have := h (show x ∘ e.symm ∈ LinearMap.ker (reindex e e Y).mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply, key0, Function.comp_assoc, h1]; exact hx)
    rw [LinearMap.mem_ker, mulVecLin_apply, key0, Function.comp_assoc, h1] at this
    exact this
  · intro h x hx
    rw [LinearMap.mem_ker, mulVecLin_apply, key0] at hx ⊢
    exact h hx
end

section
variable {A A' B : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B]

lemma kron_rx (e : A ≃ A') (σ : Matrix B B ℂ) :
    reindex (e.prodCongr (Equiv.refl B)) (e.prodCongr (Equiv.refl B))
      (identityTensorReference (A := A) σ) = identityTensorReference (A := A') σ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [identityTensorReference, reindex_apply, Matrix.kronecker, one_apply]

lemma fixedMin_rx (e : A ≃ A') (τ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) :
    fixedMin (reindex (e.prodCongr (Equiv.refl B)) (e.prodCongr (Equiv.refl B)) τ) σ =
      fixedMin τ σ := by
  unfold fixedMin
  congr 1
  ext t
  refine exists_congr fun r => and_congr_right fun _ => ?_
  have := sub_rx (e.prodCongr (Equiv.refl B)) (identityTensorReference (A := A) σ) τ
    (((Real.rpow 2 (-r) : ℝ) : ℂ))
  rw [kron_rx] at this
  change (_ • identityTensorReference (A := A') σ - _).PosSemidef ↔
    (_ • identityTensorReference (A := A) σ - τ).PosSemidef
  rw [this, psd_rx]

lemma sSFM_rx (e : A ≃ A') (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) (ε : ℝ) :
    sineSmoothFixedMin (reindex (e.prodCongr (Equiv.refl B)) (e.prodCongr (Equiv.refl B)) ρ) σ ε =
      sineSmoothFixedMin ρ σ ε := by
  set E := e.prodCongr (Equiv.refl B)
  have hball : ∀ τ, inBall (reindex E E ρ) (reindex E E τ) ε ↔ inBall ρ τ ε := by
    intro τ
    unfold inBall fidelityDistance IsSubnormalized
    rw [psd_rx, tr_rx, rootFidelity_rx]
  unfold sineSmoothFixedMin
  congr 1
  ext h
  constructor
  · rintro ⟨τ', hb, rfl⟩
    have e1 : reindex E E (reindex E.symm E.symm τ') = τ' := by ext; simp [reindex_apply]
    refine ⟨reindex E.symm E.symm τ', ?_, ?_⟩
    · rw [← hball, e1]; exact hb
    · rw [← fixedMin_rx e, e1]
  · rintro ⟨τ, hb, rfl⟩
    exact ⟨reindex E E τ, (hball τ).2 hb, (fixedMin_rx e τ σ).symm⟩
end

end X5RB
end X5mod_RB_Base

section X5mod_RB_Thm
open Matrix
open scoped ComplexOrder ENNReal

noncomputable section

namespace X5RB
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy relativeEntropyFinite supportIncluded)
open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def eU (I : Type*) : I ≃ Unit × I := (Equiv.punitProd I).symm

lemma tj_eq (ρ : Matrix I I ℂ) : trivialJoint ρ = reindex (eU I) (eU I) ρ := by
  ext x y; simp [trivialJoint, reindex_apply, eU]

lemma itr_eq (σ : Matrix I I ℂ) :
    identityTensorReference (A := Unit) σ = reindex (eU I) (eU I) σ := by
  ext x y; simp [identityTensorReference, reindex_apply, eU, Matrix.kronecker]

lemma logb_cfc (σ : Matrix I I ℂ) :
    cfc (fun x : ℝ => Real.logb 2 x) σ = (Real.log 2)⁻¹ • cfc Real.log σ := by
  rw [show (fun x : ℝ => Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * Real.log x by
    ext x; simp [Real.logb, div_eq_inv_mul]]
  exact cfc_const_mul _ _ _ (σ.finite_real_spectrum.continuousOn _)

lemma xlogb_cfc (σ : Matrix I I ℂ) :
    cfc (fun x : ℝ => x * Real.logb 2 x) σ = (Real.log 2)⁻¹ • cfc (fun x : ℝ => x * Real.log x) σ := by
  rw [show (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) by
    ext x; simp [Real.logb]; ring]
  exact cfc_const_mul _ _ _ (σ.finite_real_spectrum.continuousOn _)

lemma fvn_eq (ρ σ : Matrix I I ℂ) :
    fixedVonNeumann (trivialJoint ρ) σ = -relativeEntropy ρ σ := by
  unfold fixedVonNeumann relativeEntropy
  rw [tj_eq, itr_eq]
  by_cases h : supportedBy ρ σ
  · rw [if_pos ((supp_rx _ _ _).2 h), if_pos (show supportIncluded ρ σ from h)]
    rw [← EReal.coe_neg, EReal.coe_eq_coe_iff]
    unfold vnEntropy relativeEntropyFinite
    rw [cfc_rx, cfc_rx, rmul, tr_rx, tr_rx, logb_cfc, xlogb_cfc]
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_re, Complex.smul_re, smul_eq_mul]
    have : Real.log 2 ≠ 0 := by positivity
    field_simp
    ring
  · rw [if_neg (fun h' => h ((supp_rx _ _ _).1 h')), if_neg (show ¬ supportIncluded ρ σ from h)]
    rfl

lemma jp_eq (ρ : Matrix I I ℂ) (n : ℕ) :
    jointPower (trivialJoint ρ) n =
      reindex ((Equiv.ofUnique Unit (Fin n → Unit)).prodCongr (Equiv.refl _))
        ((Equiv.ofUnique Unit (Fin n → Unit)).prodCongr (Equiv.refl _))
        (trivialJoint (matrixPower ρ n)) := by
  ext x y; simp [jointPower, trivialJoint, reindex_apply, matrixPower]

theorem main [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ relativeUpsilon rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma +
            ((aepBlockError epsilon (relativeUpsilon rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal)) ∧
    (¬ supportedBy rho sigma → relativeEntropy rho sigma = ⊤ ∧
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma) ∧
    (1 ≤ epsilon →
      smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon = ⊥) := by
  have hT : IsDensityMatrix (trivialJoint rho) := by
    rw [tj_eq]; exact ⟨(psd_rx _ _).2 hrho.1, by rw [tr_rx]; exact hrho.2⟩
  have R10 := fixedReferenceFiniteBlock (A := Unit) (B := I) (trivialJoint rho) sigma hT hsigma
    epsilon hepsilon n hn
  have hJ : sineSmoothFixedMin (jointPower (trivialJoint rho) n) (matrixPower sigma n) epsilon =
      sineSmoothFixedMin (trivialJoint (matrixPower rho n)) (matrixPower sigma n) epsilon := by
    rw [jp_eq, sSFM_rx]
  have hD : ¬ supportedBy rho sigma → relativeEntropy rho sigma = ⊤ := fun h => by
    unfold relativeEntropy; exact if_neg (show ¬ supportIncluded rho sigma from h)
  refine ⟨fun h => ?_, fun h => ⟨hD h, by rw [hD h]; exact le_top⟩, fun h => ?_⟩
  · have := R10.1 h
    rw [hJ, fvn_eq] at this
    unfold smoothMaxRelative
    rw [mul_neg, EReal.neg_le]
    set err : ℝ := aepBlockError epsilon (relativeUpsilon rho sigma) / Real.sqrt (n : ℝ)
    rw [EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))]
    exact this
  · unfold smoothMaxRelative
    rw [← hJ, R10.2.2 h]
    rfl

end X5RB

end
end X5mod_RB_Thm


open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ relativeUpsilon rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma +
            ((aepBlockError epsilon (relativeUpsilon rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal)) ∧
    (¬ supportedBy rho sigma → relativeEntropy rho sigma = ⊤ ∧
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma) ∧
    (1 ≤ epsilon →
      smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon = ⊥) :=
  X5RB.main rho sigma hrho hsigma epsilon hepsilon n hn
