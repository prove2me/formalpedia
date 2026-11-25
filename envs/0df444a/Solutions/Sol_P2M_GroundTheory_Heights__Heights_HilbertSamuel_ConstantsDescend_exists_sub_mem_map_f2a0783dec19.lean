-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_sub_mem_map_f2a0783dec19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:30:13.201461+00:00
-- url     : https://prove2.me/submissions/92edd053-a2e6-4c0e-bed9-a1aa5e261220

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic)
    (hps : p.Separable) (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ)
    (I : Ideal A) [I.IsMaximal] (hI : I.map (algebraMap A B) ≠ ⊤) (b : B) :
    ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B) := by
  classical
  set J := I.map (algebraMap A B) with hJ
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : Algebra.FiniteType ℚ (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ I) (Ideal.Quotient.mkₐ_surjective ℚ I)
  haveI : Module.Finite ℚ (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ I)
  haveI : Algebra.IsAlgebraic ℚ (A ⧸ I) := Algebra.IsAlgebraic.of_finite ℚ _
  let σ : A ⧸ I →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set θ' := Ideal.Quotient.mk J θ with hθ'def
  have hpF : p.map (algebraMap ℚ (A ⧸ I)) = (p.map (algebraMap ℚ A)).map (algebraMap A (A ⧸ I)) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hθ' : aeval θ' (p.map (algebraMap ℚ (A ⧸ I))) = 0 := by
    rw [hpF, hθ'def, aeval_mk_map, hp, map_zero]
  have hint : IsIntegral (A ⧸ I) θ' := ⟨_, hpm.map _, hθ'⟩
  have hmem : θ' ∈ (algebraMap (A ⧸ I) (B ⧸ J)).range := by
    by_contra hn
    have h2 := (minpoly.two_le_natDegree_iff hint).2 hn
    set q := (minpoly (A ⧸ I) θ').map (σ : A ⧸ I →+* ℂ) with hq
    have hs1 : (p.map (algebraMap ℚ (A ⧸ I))).Separable := hps.map
    have hs2 : (minpoly (A ⧸ I) θ').Separable := hs1.of_dvd (minpoly.dvd _ _ hθ')
    have hsep : q.Separable := hs2.map
    have hq0 : q ≠ 0 := (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have hcard : q.roots.toFinset.card = (minpoly (A ⧸ I) θ').natDegree := by
      rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
        natDegree_map]
    obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < q.roots.toFinset.card)
    rw [Multiset.mem_toFinset, mem_roots hq0] at h₁ h₂
    obtain ⟨w₁, hw₁, hθ₁⟩ := exists_ringHom_of_root θ hgen I σ β₁ h₁
    obtain ⟨w₂, hw₂, hθ₂⟩ := exists_ringHom_of_root θ hgen I σ β₂ h₂
    exact hne (hθ₁ ▸ hθ₂ ▸ huniq w₁ w₂ (hw₁.trans hw₂.symm))
  let S : Subalgebra A B := (⊥ : Subalgebra A (B ⧸ J)).comap (Ideal.Quotient.mkₐ A J)
  have hθS : θ ∈ S := by
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show Ideal.Quotient.mkₐ A J θ ∈ (⊥ : Subalgebra A (B ⧸ J))
    have he : Ideal.Quotient.mkₐ A J θ = algebraMap A (B ⧸ J) a := by
      rw [Ideal.Quotient.mkₐ_eq_mk, ← hθ'def, ← hc, Ideal.Quotient.algebraMap_quotient_map_quotient,
        Ideal.Quotient.mk_algebraMap]
    rw [he]
    exact Subalgebra.algebraMap_mem _ a
  have hbS : b ∈ S := by
    have : Algebra.adjoin A {θ} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.2 hθS)
    exact this (hgen ▸ Algebra.mem_top)
  obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hbS
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  have he : Ideal.Quotient.mk J b = algebraMap A (B ⧸ J) a := ha.symm
  rw [he, Ideal.Quotient.mk_algebraMap]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
