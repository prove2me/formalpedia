-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMLengthParameters_proof_d4051ecf08a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:09.086304+00:00
-- url     : https://prove2.me/submissions/3394c974-b942-42c4-aa5e-a7a0c3da2c9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq_6b854b8a0529
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e

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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
namespace CMLengthParameters
theorem _root_.solution (hCM : CMRegularElement.Statement.{u})
    (hLen : LengthLocalizedQuotient.Statement.{u}) : CMLengthParameters.Statement.{u} := by
  suffices h : ∀ d : ℕ, ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime]
      (x : Fin d → B), minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
      Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
        Module.length B (B ⧸ Ideal.span (Set.range x)) =
          Module.length (Localization.AtPrime P) (Localization.AtPrime P) from
    fun B _ _ P _ d x => h d B P x
  intro d
  induction d with
  | zero =>
    intro B _ _ P _ x _ _ hmax
    have hx : Ideal.span (Set.range x) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hx, bot_sup_eq] at hmax
    subst hmax
    rw [hx, length_localization_maximalIdeal]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
  | succ k ih =>
    intro B _ _ P _ x hmin hdim hmax
    obtain ⟨hyP, hQ₀, hdimQ⟩ := notMem_and_isPrime_sup_span x hdim hmax
    set y := x 0 with hy
    set Q₀ := P ⊔ Ideal.span {y} with hQ₀def
    have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    have hnzd : ∀ s ∉ P, s ∈ nonZeroDivisors B := fun s hs =>
      mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq hCM hmin hs
    have hyQ : Ideal.span {y} ≤ Q₀ := le_sup_right

    have hB'CM : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y}) := (hCM B y (hxm 0) fun p hp => by
      rw [hmin, Set.mem_singleton_iff] at hp
      rwa [hp]).2
    set f := Ideal.Quotient.mk (Ideal.span {y}) with hf
    have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ Q₀ := by rw [hf, Ideal.mk_ker]; exact hyQ
    set P' := Q₀.map f with hP'def
    have hP' : P'.IsPrime := Ideal.map_isPrime_of_surjective hfs hker
    have hcomap : P'.comap f = Q₀ := by
      rw [hP'def, Ideal.comap_map_of_surjective' f hfs, sup_eq_left.2 hker]

    have hall : ∀ q : Ideal (B ⧸ Ideal.span {y}), q.IsPrime → P' ≤ q := by
      intro q hq
      have hqc : (q.comap f).IsPrime := Ideal.comap_isPrime f q
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.comap f)
      have hpP : p = P := by
        have : p ∈ minimalPrimes B := hp
        rw [hmin, Set.mem_singleton_iff] at this
        exact this
      subst hpP
      have hyq : Ideal.span {y} ≤ q.comap f := fun z hz => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact q.zero_mem
      rw [hP'def, Ideal.map_le_iff_le_comap]
      exact sup_le hpq hyq
    have hmin' : minimalPrimes (B ⧸ Ideal.span {y}) = {P'} := by
      ext q
      rw [Set.mem_singleton_iff]
      constructor
      · intro hq
        exact le_antisymm (hq.2 ⟨hP', bot_le⟩ (hall q hq.1.1)) (hall q hq.1.1)
      · rintro rfl
        exact ⟨⟨hP', bot_le⟩, fun q hq _ => hall q hq.1⟩
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {y}) ⧸ P') = (k : ℕ) := by
      rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hyQ)]
      exact hdimQ

    set x' : Fin k → B ⧸ Ideal.span {y} := fun j => f (x j.succ) with hx'
    have hmB' : (maximalIdeal B).map f = maximalIdeal (B ⧸ Ideal.span {y}) :=
      map_maximalIdeal_of_surjective f hfs
    have hmax' : Ideal.span (Set.range x') ⊔ P' = maximalIdeal (B ⧸ Ideal.span {y}) := by
      apply le_antisymm
      · refine sup_le (Ideal.span_le.2 ?_) (IsLocalRing.le_maximalIdeal hP'.ne_top)
        rintro _ ⟨j, rfl⟩
        rw [← hmB']
        exact Ideal.mem_map_of_mem f (hxm _)
      · rw [← hmB', Ideal.map_le_iff_le_comap, ← hmax]
        refine sup_le (Ideal.span_le.2 ?_) fun p hp => ?_
        · rintro _ ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
          | succ j => exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_left hp))
    have key := ih (B ⧸ Ideal.span {y}) P' x' hmin' hdim' hmax'
    rw [hLen B P y hmin hnzd hyP P' hcomap] at key
    rw [← key]

    have hyx : Ideal.span {y} ≤ Ideal.span (Set.range x) :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨0, rfl⟩)
    have hJ : (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y})) = Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine span_range_eq_span_range_succ _ ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    calc Module.length B (B ⧸ Ideal.span (Set.range x))
        = Module.length B ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          (DoubleQuot.quotQuotEquivQuotOfLEₐ B hyx).toLinearEquiv.length_eq.symm
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸ Ideal.span (Set.range x')) := by
          rw [hJ]
end CMLengthParameters
end GroundTheory.Heights₂.Heights
