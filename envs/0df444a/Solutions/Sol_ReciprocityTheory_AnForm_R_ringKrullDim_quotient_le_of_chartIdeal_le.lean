-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:40.837413+00:00
-- url     : https://prove2.me/submissions/d9bd5d01-65bd-41f1-92c4-d35c15946040

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_aeval_smul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime]
    (h𝔮 : chartIdeal P p ≤ 𝔮) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≤ e := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  let θ : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := aeval (fun q => (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q)
  have hy : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), aeval y f = C (Ideal.Quotient.mk 𝔮 f) := by
    intro f
    have : (aeval y : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
        (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [y, MvPolynomial.algebraMap_eq]
    rw [this]
    simp [MvPolynomial.algebraMap_eq]
  have hPθ : P ≤ RingHom.ker θ := by
    obtain ⟨S, hS, hPS⟩ := hP
    have hle : Ideal.span S ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfP : f ∈ P := by rw [hPS]; exact Ideal.subset_span hf
      have hf𝔮 : f ∈ 𝔮 := h𝔮 (Ideal.mem_sup_left hfP)
      show θ f = 0
      simp only [θ]
      rw [aeval_smul_of_isMultiHomog ha (X : K → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) y, hy,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf𝔮, map_zero, mul_zero]
    rw [hPS]
    exact hle
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le hPθ
  have hdimR : ringKrullDim θ.range ≤ ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim Q hQmin]
    let g : (MvPolynomial (Σ k, ι k) ℂ) ⧸ Q →+* θ.range := Ideal.Quotient.lift Q (θ.rangeRestrict : (MvPolynomial (Σ k, ι k) ℂ) →+* θ.range)
      (fun a ha => Subtype.ext (by simpa using hQle ha))
    refine ringKrullDim_le_of_surjective g ?_
    intro x
    obtain ⟨a, ha⟩ := θ.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk Q a, ha⟩
  have : Algebra.FiniteType ℂ θ.range :=
    Algebra.FiniteType.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := θ.range)
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).mpr (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ θ.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ θ.range).mpr (algebraMap ℂ θ.range).injective
  have : FaithfulSMul θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr Subtype.val_injective
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) + trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)

  have h1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : (MvPolynomial (Σ k, ι k) ℂ)) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h𝔮 (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXk : ∀ k, (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) ∈ θ.range := by
    intro k
    refine (θ.mem_range).mpr ⟨X ⟨k, p k⟩, ?_⟩
    simp only [θ, y, aeval_X, h1, map_one, mul_one]
  have hXq : ∀ q, (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q ∈ θ.range := fun q =>
    (θ.mem_range).mpr ⟨X q, by simp only [θ, aeval_X]⟩
  let AC := Subalgebra.algebraicClosure θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ t ∈ θ.range, t ∈ AC := fun t ht =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (isAlgebraic_algebraMap (⟨t, ht⟩ : θ.range))
  have hyAC : ∀ q, y q ∈ AC := fun q =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXk q.1)))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXq q))))
  have hCAC : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => C (Ideal.Quotient.mk 𝔮 f) ∈ AC) f ?_ ?_ ?_
    · intro c
      apply hRAC
      refine (θ.mem_range).mpr ⟨C c, ?_⟩
      simp only [θ, aeval_C, MvPolynomial.algebraMap_apply]
      rfl
    · intro f g hf hg
      rw [map_add, map_add]
      exact AC.add_mem hf hg
    · intro f q hf
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    refine MvPolynomial.induction_on (motive := fun t => t ∈ AC) t ?_ ?_ ?_
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    · intro f g hf hg
      exact AC.add_mem hf hg
    · intro f k hf
      exact AC.mul_mem hf (hRAC _ (hXk k))
  have : Algebra.IsAlgebraic θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ θ.range + trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ θ.range
  have h0 : trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  rw [hRdim] at hdimR
  have hsR : sR ≤ e + Fintype.card K := by exact_mod_cast hdimR
  rw [hAdim]
  exact_mod_cast (by omega : sA ≤ e)
end ReciprocityTheory.AnForm.R
