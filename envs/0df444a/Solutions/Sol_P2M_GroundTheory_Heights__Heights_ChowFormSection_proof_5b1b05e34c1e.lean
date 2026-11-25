-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:42.68373+00:00
-- url     : https://prove2.me/submissions/ea37a24a-3f20-4b7c-a305-2020c05d9928

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_iff_656fe0f0fba5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_dvd_of_forall_emultiplicity_le_e0492f3f8d14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ChowFormSection
theorem _root_.solution (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncIdealPrime.Statement) (h₅ : SectionOrder.Statement) :
    ChowFormSection.Statement := by
  intro F _ _ n e I f u hI hf hu
  classical
  obtain ⟨hh0, hord⟩ := h₅ F n e I f u hI hf hu
  have hdim := h₁ F n (e + 1) I f hI hf
  have hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    by_contra h
    exact hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
  have hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    h₂ F n e I W u hI hdim hu (hcomp W hW)
  have hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g := fun W hW =>
    h₃ F n e W (hW1 W hW).1 (hW1 W hW).2
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    simp only [g, dif_pos (hex W hW)]
    exact (hex W hW).choose_spec
  have hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W} := fun W hW =>
    (isChowForm_iff.mp (hg W hW)).2
  have hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W) := by
    intro W hW
    have hp := h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant
    rw [hspan W hW] at hp
    exact (Ideal.span_singleton_prime (isChowForm_iff.mp (hg W hW)).1).mp hp
  set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr
  have hPr0 : Pr ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero
  have hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u) := by
    intro q hq
    have hqp : Prime q := hq.prime
    rw [hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [emultiplicity_pow hqp]
    split_ifs with hs
    · have hass : Associated q (g W) := by
        rw [← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]
      rw [← emultiplicity_eq_of_associated_left hass,
        (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self,
        mul_one]
    · have : emultiplicity q (g W) = 0 := by
        rw [emultiplicity_eq_zero]
        intro hdvd
        apply hs
        rw [hspan W hW, Ideal.span_singleton_eq_span_singleton]
        exact hq.associated_of_dvd (hgprime W hW).irreducible hdvd
      rw [this, mul_zero]
  have hass : Associated Pr (specFirst f u) :=
    associated_of_dvd_dvd
      (dvd_of_forall_emultiplicity_le hPr0 hh0 fun q hq => (hmult q hq).le)
      (dvd_of_forall_emultiplicity_le hh0 hPr0 fun q hq => (hmult q hq).ge)
  obtain ⟨v, hv⟩ := hass
  obtain ⟨c, hc, hvc⟩ := (isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp
    v.isUnit
  refine ⟨c, hc.ne_zero, g, hg, ?_⟩
  rw [← hv, hvc, mul_comm]
end ChowFormSection
end GroundTheory.Heights₂.Heights
