-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:51.463337+00:00
-- url     : https://prove2.me/submissions/0c451a1f-8c21-48e2-9ba8-d7f9fbf8a44f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_withBot_natCast_le_of_add_one_le_3cfdfc22d150
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain


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
theorem _root_.solution {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by
  have hPm : P ≤ maximalIdeal B := hmax ▸ le_sup_right
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hA := maximalIdeal_quotient_eq_span x hmax
  have hy : x 0 ∉ P := by
    intro hyP
    have h0 : Ideal.Quotient.mk P (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hyP
    have hle := ringKrullDim_le_spanFinrank_maximalIdeal (B ⧸ P)
    rw [hA, span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk P (x i)) h0, hdim] at hle
    have hk := spanFinrank_span_range_le (fun j : Fin k => Ideal.Quotient.mk P (x j.succ))
    have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := hle.trans (by exact_mod_cast hk)
    have h3 : k + 1 ≤ k := by exact_mod_cast h2
    omega
  set Q₀ := P ⊔ Ideal.span {x 0} with hQ₀
  have hQ₀m : Q₀ ≤ maximalIdeal B := sup_le hPm ((Ideal.span_singleton_le_iff_mem _).2 (hxm 0))
  have hmaxQ : Ideal.span (Set.range x) ⊔ Q₀ = maximalIdeal B :=
    le_antisymm (sup_le (hmax ▸ le_sup_left) hQ₀m) (hmax ▸ sup_le_sup_left le_sup_left _)
  have : Nontrivial (B ⧸ Q₀) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hQ₀m))
  have : IsLocalRing (B ⧸ Q₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q₀) Ideal.Quotient.mk_surjective
  have hA' := maximalIdeal_quotient_eq_span x hmaxQ
  have h0' : Ideal.Quotient.mk Q₀ (x 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk Q₀ (x i)) h0'] at hA'
  have hfin : (maximalIdeal (B ⧸ Q₀)).spanFinrank ≤ k := hA' ▸ spanFinrank_span_range_le _
  have hge : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Q₀) := by
    have e : (B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P (x 0)} ≃+* B ⧸ Q₀ :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x 0}))
    have hj : ({Ideal.Quotient.mk P (x 0)} : Set (B ⧸ P)) ⊆ Ring.jacobson (B ⧸ P) := by
      rw [Set.singleton_subset_iff, IsLocalRing.ringJacobson_eq_maximalIdeal, hA]
      exact Ideal.subset_span ⟨0, rfl⟩
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hj
    rw [hdim, Set.encard_singleton, ringKrullDim_eq_of_ringEquiv e] at h
    exact withBot_natCast_le_of_add_one_le (by exact_mod_cast h)
  have hle : ringKrullDim (B ⧸ Q₀) ≤ ((k : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hfin)
  have : IsRegularLocalRing (B ⧸ Q₀) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ((by exact_mod_cast hfin :
      ((maximalIdeal (B ⧸ Q₀)).spanFinrank : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞)).trans hge)
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := B ⧸ Q₀)
  exact ⟨hy, (Ideal.Quotient.isDomain_iff_prime Q₀).1 inferInstance, le_antisymm hle hge⟩
end GroundTheory.Heights₂.Heights
