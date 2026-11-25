-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:50.079856+00:00
-- url     : https://prove2.me/submissions/796b334b-6926-4c5e-80f3-18eff8d073a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_comap_ne_bot_d935be84853d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878


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
universe u v w
open GroundTheory.Heights₂.Heights.GenericFreeness
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (coeff 0 x) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : coeff 0 x ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq fun x ↦ ((aeval z).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc
end GroundTheory.Heights₂.Heights.GenericFreeness
