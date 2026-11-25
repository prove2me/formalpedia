-- Prove2me | solution 1 for ReciprocityTheory.Gal.exists_frob_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:25.432557+00:00
-- url     : https://prove2.me/submissions/501487a8-152b-4054-bb9a-03efbc4c074c

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Theorems.Thm_ReciprocityTheory_Gal_exists_den
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_under_primeBelow
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance
  haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ
  have hσQ' : σ • Q = Q := hσQ
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q := Fintype.card_eq_nat_card
  have hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (σ • b) =
        Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)
    have h2 : σ • b - b ^ q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]
    exact h2
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  refine ⟨σ, hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hcs := hcong ⟨s, hs.tower_top⟩
  have hct := hcong ⟨t, ht.tower_top⟩
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv
end ReciprocityTheory.Gal
