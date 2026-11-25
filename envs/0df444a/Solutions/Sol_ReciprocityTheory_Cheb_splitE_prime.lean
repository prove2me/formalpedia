-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:08.337142+00:00
-- url     : https://prove2.me/submissions/1435b0ad-6665-4cb7-8e0f-9b5b9dc2646d

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_mem_H
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_one_lt_Nrm
import Theorems.Thm_ReciprocityTheory_Cheb_splitA_unram
import Theorems.Thm_ReciprocityTheory_Cheb_splitD_frob
import Theorems.Thm_ReciprocityTheory_Cheb_under_asIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver q.asIdeal] :
    Q.ramificationIdx (𝓞 E) = 1 ∧ Q.inertiaDeg (𝓞 E) = 1 ∧ Ideal.absNorm Q = Nrm q := by
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q
  obtain ⟨⟨P, hPp, hPl⟩⟩ := Q.nonempty_primesOver (S := 𝓞 (CyclotomicField l E))
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ0 P
  have hPq : P.LiesOver q.asIdeal := Ideal.LiesOver.trans P Q q.asIdeal
  let P' : Prm (CyclotomicField l E) := ⟨P, hPp, hP0⟩
  have hund : under (E := E) P' = q := by
    ext1; rw [under_asIdeal]; exact (Ideal.over_def P q.asIdeal).symm
  have he : Q.ramificationIdx (𝓞 E) = 1 := by
    have h1 := splitA_unram E l q P' hund hl
    have h2 := Ideal.ramificationIdx_tower (R := 𝓞 E) Q P
    change P.ramificationIdx (𝓞 E) = 1 at h1
    rw [h2] at h1
    exact Nat.eq_one_of_mul_eq_one_right h1
  obtain ⟨σ, hσζ, hσx⟩ := splitD_frob E l q P' hund hl
  have hσH : σ ∈ splitEH hirr χ := splitE_mem_H hirr χ σ _ hσζ hq
  have hfix : ∀ x : 𝓞 K, x - x ^ Nrm q ∈ Q := by
    intro x
    obtain ⟨y, hy, hyP⟩ := hσx (algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x)
    have hxy : y = algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x := by
      apply RingOfIntegers.ext
      rw [hy]
      have : ((algebraMap (𝓞 K) (𝓞 (CyclotomicField l E)) x : 𝓞 _) : CyclotomicField l E) =
          ((x : K) : CyclotomicField l E) := rfl
      rw [this]
      exact hK (x : K) σ hσH
    rw [hxy] at hyP
    rw [Ideal.over_def P Q]
    simpa [Ideal.under, map_sub, map_pow] using hyP
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  have : q.asIdeal.IsMaximal := q.isMaximal
  have hN := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver Q q.asIdeal q.isPrime q.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hN
  have h2 : 1 < Nrm q := splitE_one_lt_Nrm q
  let : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (𝓞 K ⧸ Q) := Fintype.ofFinite _
  have hcard : Ideal.absNorm Q ≤ Nrm q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← Finset.card_univ]
    rw [← FiniteField.X_pow_card_sub_X_natDegree_eq (𝓞 K ⧸ Q) h2]
    apply Polynomial.card_le_degree_of_subset_roots
    intro z _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h2)]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have := (Ideal.Quotient.eq_zero_iff_mem).2 (hfix x)
    rw [map_sub, map_pow, sub_eq_zero] at this
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← this, sub_self]
  have hf0 : 0 < Q.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos Q (𝓞 E)
  have hf : Q.inertiaDeg (𝓞 E) = 1 := by
    have h3 : Nrm q ^ Q.inertiaDeg (𝓞 E) ≤ Nrm q ^ 1 := by
      rw [pow_one]; unfold Nrm; rw [← hN]; exact hcard
    have := (Nat.pow_le_pow_iff_right h2).1 h3
    omega
  refine ⟨he, hf, ?_⟩
  rw [hN, hf, pow_one]; rfl
end ReciprocityTheory.Cheb
