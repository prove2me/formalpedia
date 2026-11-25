-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:24.376373+00:00
-- url     : https://prove2.me/submissions/4938e8c3-2133-4b0c-af5c-065d2dc24d55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___injective_9eafdcb1cad6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_sT_ne_zero_d0219b53b8a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (h₂ : IncidenceGeneric.Statement) (h₃ : IncIdealBelow.Statement)
    (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (hQ : IsProjPrime Q) (hg : IsChowForm Q (e + 1) g) :
    ∃ (Ω : Type) (_ : Field Ω) (Ψ : SecR Q e →+* Ω),
      Function.Injective (Ψ.comp (algebraMap (MvPolynomial (Par e n) k) (SecR Q e))) ∧
        ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0 := by
  have := hQ.isPrime
  obtain ⟨j0, hj0⟩ := hQ.isRelevant
  have hξ : ∀ l, X l ∉ Q → genPt Q l ≠ 0 := fun l hl =>
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin n) k ⧸ Q) (Fn Q))).mpr
      fun h => hl (Ideal.Quotient.eq_zero_iff_mem.mp h)
  set c : Fin n → Fn Q := Pi.single j0 (genPt Q j0)⁻¹ with hcdef
  have hc : ∑ j, c j * genPt Q j = 1 := by
    simp [c, Pi.single_apply, inv_mul_cancel₀ (hξ j0 hj0)]
  have hσ : Function.Injective (gsub Q e c) := by
    refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
    have hmem := (h₂ k n e Q c hc p).mpr hp
    rw [h₃ k n e Q g hQ hg] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hs := sT_ne_zero Q e j0 (hξ j0 hj0)
  have hle := secIdeal_le_ker Q e hQ.isHomog c hc hs
  refine ⟨Om Q e, inferInstance,
    Ideal.Quotient.lift _ (Ψt Q e c) (fun a ha => RingHom.mem_ker.mp (hle ha)), ?_, fun l hl => ?_⟩
  · intro r r' h
    refine ρ_injective Q e c hσ (IsFractionRing.injective (Tgt Q e) (Om Q e) ?_)
    have hr : ∀ r : MvPolynomial (Par e n) k, algebraMap _ (SecR Q e) r =
        Ideal.Quotient.mk (secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
          (X : Par e n → MvPolynomial (Par e n) k)) (C r) := fun _ => rfl
    simp only [RingHom.comp_apply, hr, Ψt, Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_C] at h
    exact h
  · show Ψt Q e c (X l) ≠ 0
    rw [Ψt, coe_eval₂Hom, eval₂_X, xs]
    refine mul_ne_zero ?_ (inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr hs))
    rw [ι, RingHom.comp_apply, RingHom.comp_apply]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr
      (by simpa using hξ l hl)
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
