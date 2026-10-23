-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.degradingRangeContainment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:14:12.764991+00:00
-- url     : https://prove2.me/submissions/5492c296-e062-400b-99c9-fc6d022d070b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix

/-- Range containment for a Hermitian `Y`: if `ker Y ⊆ ker M` and `M` is Hermitian,
then every `M x` lies in the range of `Y` (via the spectral theorem). -/
lemma x8_range {I : Type} [Fintype I] [DecidableEq I] (Y M : Matrix I I ℂ) (hY : Y.IsHermitian)
    (hM : Mᴴ = M) (h : ∀ u, Y *ᵥ u = 0 → M *ᵥ u = 0) (x : I → ℂ) :
    ∃ z, Y *ᵥ z = M *ᵥ x := by
  set W : Matrix I I ℂ := (hY.eigenvectorUnitary : Matrix I I ℂ) with hWdef
  set d : I → ℂ := RCLike.ofReal ∘ hY.eigenvalues with hd
  have hs : Y = W * diagonal d * star W := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hWW : star W * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * star W = 1 := Unitary.coe_mul_star_self _
  set v := star W *ᵥ (M *ᵥ x) with hvdef
  have hv : ∀ k, d k = 0 → v k = 0 := by
    intro k hk
    have hk' : hY.eigenvalues k = 0 := by simpa [hd] using hk
    have he : Y *ᵥ ⇑(hY.eigenvectorBasis k) = 0 := by
      rw [hY.mulVec_eigenvectorBasis, hk', zero_smul]
    have hMe := h _ he
    have : v k = star ⇑(hY.eigenvectorBasis k) ⬝ᵥ (M *ᵥ x) := by
      simp only [hvdef, mulVec, dotProduct, hWdef, star_apply, Matrix.star_apply,
        IsHermitian.eigenvectorUnitary_apply, Pi.star_apply]
    rw [this, dotProduct_mulVec, ← conjTranspose_conjTranspose M, ← star_mulVec, hM, hMe,
      star_zero, zero_dotProduct]
  refine ⟨(W * diagonal (fun k => (d k)⁻¹) * star W) *ᵥ (M *ᵥ x), ?_⟩
  have hprod : (W * diagonal d * star W) * (W * diagonal (fun k => (d k)⁻¹) * star W) =
      W * diagonal (fun k => d k * (d k)⁻¹) * star W := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star W) W, hWW, Matrix.one_mul, ← Matrix.mul_assoc (diagonal d),
      diagonal_mul_diagonal]
  have hdv : diagonal (fun k => d k * (d k)⁻¹) *ᵥ v = v := by
    funext k
    rw [mulVec_diagonal]
    by_cases hk : d k = 0
    · rw [hv k hk, mul_zero]
    · rw [mul_inv_cancel₀ hk, one_mul]
  rw [hs, mulVec_mulVec, hprod, ← mulVec_mulVec, ← mulVec_mulVec, ← hvdef, hdv, hvdef,
    mulVec_mulVec, hWW', one_mulVec]

/-- Kernel transfer through a Kraus map: if `Σ K P Kᴴ` kills `u` and `P ⪰ 0`, then so does
`Σ K φφᴴ Kᴴ` for every `φ = P x` in the range of `P`. -/
lemma x8_ker {B E : Type} [Fintype B] [Fintype E] {m : ℕ} (K : Fin m → Matrix E B ℂ)
    (P : Matrix B B ℂ) (hP : P.PosSemidef) (x : B → ℂ) (u : E → ℂ)
    (hu : (∑ j, K j * P * (K j)ᴴ) *ᵥ u = 0) :
    (∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ) *ᵥ u = 0 := by
  have hterm : ∀ j, star u ⬝ᵥ (K j * P * (K j)ᴴ) *ᵥ u =
      star ((K j)ᴴ *ᵥ u) ⬝ᵥ P *ᵥ ((K j)ᴴ *ᵥ u) := by
    intro j
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  have h0 : ∑ j, star ((K j)ᴴ *ᵥ u) ⬝ᵥ P *ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    have := congrArg (fun w => star u ⬝ᵥ w) hu
    simp only [sum_mulVec, dotProduct_sum, dotProduct_zero, hterm] at this
    exact this
  have hz : ∀ j, P *ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    intro j
    rw [← hP.dotProduct_mulVec_zero_iff]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hP.dotProduct_mulVec_nonneg _)).1 h0 j
      (Finset.mem_univ _)
  rw [sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, vecMulVec_mulVec]
  have : star (P *ᵥ x) ⬝ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    rw [star_mulVec, ← dotProduct_mulVec, hP.1.eq, hz j, dotProduct_zero]
  rw [this]
  simp

lemma x8_pd {I : Type} (ψ : EuclideanSpace ℂ I) :
    QAlgorithms.pureDensity ψ = vecMulVec (fun i => ψ i) (star (fun i => ψ i)) := by
  ext i j
  simp [QAlgorithms.pureDensity, vecMulVec_apply]

lemma x8_tr_psd {B E : Type} [Fintype B] [Fintype E] (v : B × E → ℂ) :
    (QAlgorithms.traceRight (vecMulVec v (star v))).PosSemidef := by
  have : QAlgorithms.traceRight (vecMulVec v (star v)) =
      ∑ e, vecMulVec (fun b => v (b, e)) (star (fun b => v (b, e))) := by
    ext b b'
    simp [QAlgorithms.traceRight, vecMulVec_apply, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun e _ => posSemidef_vecMulVec_self_star _

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_main {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (D : Superop B E) (hD : IsChannel D)
    (hdegrade : ∀ rho, D (receiverChannel U rho) = complementaryChannel U rho)
    (psi : EuclideanSpace ℂ A) (hpsi : IsState psi)
    (phi : EuclideanSpace ℂ B)
    (hphi : (fun b => phi b) ∈ matrixRange (receiverChannel U (pureDensity psi))) :
    matrixRange (D (pureDensity phi)) ≤ matrixRange (complementaryChannel U (pureDensity psi)) := by
  obtain ⟨m, K, -, hDK⟩ := hD
  set P := receiverChannel U (pureDensity psi) with hPdef
  have hP : P.PosSemidef := by
    rw [hPdef, receiverChannel, x8_pd, mul_vecMulVec, vecMulVec_mul]
    have : star (fun i => psi i) ᵥ* Uᴴ = star (U *ᵥ fun i => psi i) := by
      rw [star_mulVec]
    rw [this]
    exact x8_tr_psd _
  obtain ⟨x, hx⟩ := hphi
  rw [Matrix.toLin'_apply] at hx
  have hY : complementaryChannel U (pureDensity psi) = ∑ j, K j * P * (K j)ᴴ := by
    rw [← hdegrade, hDK]; rfl
  have hM : D (pureDensity phi) =
      ∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ := by
    rw [hDK, x8_pd, hx]; rfl
  have hYh : (∑ j, K j * P * (K j)ᴴ).IsHermitian :=
    (posSemidef_sum _ fun j _ => hP.mul_mul_conjTranspose_same (K j)).1
  have hMh : (∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ).IsHermitian :=
    (posSemidef_sum _ fun j _ =>
      (posSemidef_vecMulVec_self_star (P *ᵥ x)).mul_mul_conjTranspose_same (K j)).1
  rw [hY, hM]
  rintro w ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := x8_range _ _ hYh hMh.eq (fun u hu => x8_ker K P hP x u hu) y
  exact ⟨z, by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hz]⟩

end QAlgorithms.Papers.Independent.Gap20.P19



open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P19 in
/-- Lemma 9, PDF pp.16–17. The contained vector need not be normalized;
its zero case gives the zero range. The degrader is CPTP on all operators. -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (D : Superop B E) (hD : IsChannel D)
    (hdegrade : ∀ rho, D (receiverChannel U rho) = complementaryChannel U rho)
    (psi : EuclideanSpace ℂ A) (hpsi : IsState psi)
    (phi : EuclideanSpace ℂ B)
    (hphi : (fun b => phi b) ∈ matrixRange (receiverChannel U (pureDensity psi))) :
    matrixRange (D (pureDensity phi)) ≤ matrixRange (complementaryChannel U (pureDensity psi)) :=
  x8_main U hU D hD hdegrade psi hpsi phi hphi



