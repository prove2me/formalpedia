-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_prod_embForm_dvd_99f82f2e3334
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:36.830824+00:00
-- url     : https://prove2.me/submissions/9695a884-8ae9-4720-be32-d3775e6ef2f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_embForm_1ef6dfeea45a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_eq_of_embForm_dvd_53e4b6a641c5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution [Fintype (L →ₐ[E] K)] (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {p : MvPolynomial (Fin n) K}
    (h : ∀ σ : L →ₐ[E] K, embForm σ x ∣ p) : ∏ σ : L →ₐ[E] K, embForm σ x ∣ p := by
  classical
  suffices ∀ s : Finset (L →ₐ[E] K), ∏ σ ∈ s, embForm σ x ∣ p from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    obtain ⟨q, hq⟩ := ih
    rw [Finset.prod_insert has]
    have hp : Prime (embForm a x) := (irreducible_embForm a ht).prime
    have hd : embForm a x ∣ (∏ σ ∈ s, embForm σ x) * q := hq ▸ h a
    rcases hp.dvd_or_dvd hd with h1 | h1
    · obtain ⟨σ, hσ, hdσ⟩ := (hp.dvd_finsetProd_iff _).mp h1
      exact absurd (eq_of_embForm_dvd hgen ht hdσ ▸ hσ) has
    · obtain ⟨q', rfl⟩ := h1
      exact ⟨q', by rw [hq]; ring⟩
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
