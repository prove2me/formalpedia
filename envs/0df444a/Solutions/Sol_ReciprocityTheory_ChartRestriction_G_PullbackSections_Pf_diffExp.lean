-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:34.14028+00:00
-- url     : https://prove2.me/submissions/a70e2caa-1645-4e68-aa96-9670f0c0de1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_smul_differentIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_smul_span_nat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_count_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_natCast_ne_zero_oe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_span_nat_ne_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_of_mem_factors_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_padicValNat_absNorm_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_absNorm_span_nat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_liesOver_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution : DiffExpSt := by
  intro E _ _ _ ℓ a m hℓ hm hd P hP hl
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  classical
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) ℓ (Ideal.mem_bot.mp hl)
  have hnorm : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = (discr E).natAbs :=
    NumberField.absNorm_differentIdeal E (𝓞 E)
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hnorm
    exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp hnorm.symm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero ℓ)
  have hA : padicValNat ℓ (Ideal.absNorm (differentIdeal ℤ (𝓞 E))) = a := by
    rw [hnorm, hd, padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hn : padicValNat ℓ (Ideal.absNorm (Ideal.span {(ℓ : 𝓞 E)})) = Module.finrank ℚ E := by
    rw [absNorm_span_nat, padicValNat.prime_pow]
  have htrans : ∀ Q ∈ (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset,
      ∃ σ : E ≃ₐ[ℚ] E, σ • P = Q := by
    intro Q hQ
    obtain ⟨hQp, -, hlQ⟩ := of_mem_factors_span ℓ (Multiset.mem_toFinset.mp hQ)
    haveI := hP
    haveI := hQp
    have hPQ : P.under ℤ = Q.under ℤ := by
      rw [← (liesOver_span E ℓ hℓ hP hl).over, ← (liesOver_span E ℓ hℓ hQp hlQ).over]
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := ℤ) (B := 𝓞 E) (G := E ≃ₐ[ℚ] E) P Q hPQ
    exact ⟨σ, hσ.symm⟩
  have hN : ∀ (σ : E ≃ₐ[ℚ] E) (Q : Ideal (𝓞 E)), Ideal.absNorm (σ • Q) = Ideal.absNorm Q := by
    intro σ Q
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv Q (σ • Q) (MulSemiringAction.toRingEquiv _ _ σ)
      (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv.symm
  have hconst : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (∀ σ : E ≃ₐ[ℚ] E, σ • X = X) →
      padicValNat ℓ (Ideal.absNorm X) =
        (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset.card *
          ((normalizedFactors X).count P * padicValNat ℓ (Ideal.absNorm P)) := by
    intro X hX hXσ
    rw [padicValNat_absNorm_eq_sum ℓ hX,
      Finset.sum_congr rfl (g := fun _ => (normalizedFactors X).count P * padicValNat ℓ (Ideal.absNorm P)),
      Finset.sum_const, smul_eq_mul]
    intro Q hQ
    obtain ⟨σ, rfl⟩ := htrans Q hQ
    obtain ⟨hQp, hQ0, -⟩ := of_mem_factors_span ℓ (Multiset.mem_toFinset.mp hQ)
    have hc := count_smul σ hP hP0 hQp hQ0 hX
    rw [hXσ σ] at hc
    rw [hN σ P, hc]
  have h1 := hconst _ hD0 (fun σ => smul_differentIdeal σ)
  have h2 := hconst _ (span_nat_ne_bot ℓ) (fun σ => smul_span_nat σ ℓ)
  rw [hA] at h1
  rw [hn] at h2
  rw [h1, h2]
  ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
