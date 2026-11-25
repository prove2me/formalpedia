-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:06.708463+00:00
-- url     : https://prove2.me/submissions/e82bc31f-66ab-49a5-86b1-9f33146176fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_coeff_aeval_C_mul_X_pow_fd86e2680e3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) (N : K → ℕ)
    (u : J → MRing ι R) (hu : ∀ j, IsMultiHomog (u j) N) : IsMultiHomogIdeal (blowUpOf P u) := by
  classical
  set w := blockWeight (extIdx ι J)
  set L := blowUpDegMap N
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  set ωL : (Σ o, extIdx ι J o) → K → ℕ := fun v => L (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hL : ∀ d, Finsupp.weight ωL d = L (Finsupp.weight w d) := fun d =>
    weight_comp_addMonoidHom_apply w L d

  have hθ : ∀ v, IsMultiHomog (blowUpAtOne u v) (ωL v) := by
    rintro ⟨o, i⟩
    cases o with
    | none =>
      have : ωL ⟨none, i⟩ = N := by
        funext k
        simp [ωL, L, w, blowUpDegMap, blockWeight]
      rw [this]
      exact hu i
    | some k =>
      have : ωL ⟨some k, i⟩ = blockWeight ι ⟨k, i⟩ := by
        funext k'
        simp [ωL, L, w, blowUpDegMap, blockWeight, Pi.single_apply]
      rw [this]
      exact isWeightedHomogeneous_X R _ _

  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hcoeff : ∀ r n, (aeval (R := R) (blowUpSubst P u) r).coeff n =
      Ideal.Quotient.mk P (aeval (blowUpAtOne u) (weightedHomogeneousComponent ωT n r)) := by
    intro r n
    rw [hsubst, coeff_aeval_C_mul_X_pow, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply,
      comp_aeval]

  have key : ∀ D m : Option K → ℕ, D = m ↔ L D = L m ∧ D none = m none := by
    intro D m
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext o
      cases o with
      | none => exact h2
      | some k =>
        have := congrFun h1 k
        simp only [L, blowUpDegMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h2] at this
        omega
  have hsplit : ∀ (m : Option K → ℕ) (n : ℕ) (r : MRing (extIdx ι J) R),
      weightedHomogeneousComponent ωT n (weightedHomogeneousComponent w m r) =
        if n = m none then weightedHomogeneousComponent ωL (L m) (weightedHomogeneousComponent ωT n r)
        else 0 := by
    intro m n r
    ext d
    split_ifs with hn
    · simp only [coeff_weightedHomogeneousComponent, hT, hL, key (Finsupp.weight w d) m]
      subst hn
      by_cases h1 : Finsupp.weight w d none = m none <;> by_cases h2 : L (Finsupp.weight w d) = L m <;>
        simp [h1, h2]
    · simp only [coeff_weightedHomogeneousComponent, hT, key (Finsupp.weight w d) m, coeff_zero]
      by_cases h1 : Finsupp.weight w d none = n
      · have : ¬ Finsupp.weight w d none = m none := fun h => hn (h1.symm.trans h)
        simp [h1, hn]
      · simp [h1]
  intro p hp m
  rw [blowUpOf, RingHom.mem_ker] at hp ⊢
  refine Polynomial.ext fun n => ?_
  rw [hcoeff, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem, hsplit]
  split_ifs with hn
  · rw [aeval_weightedHomogeneousComponent_of_forms ωL _ hθ]
    apply hP
    have := hcoeff p n
    rw [hp, Polynomial.coeff_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  · rw [map_zero]
    exact P.zero_mem
end GroundTheory.Heights₂.Heights.NumbersDVR
