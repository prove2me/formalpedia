-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:31.560442+00:00
-- url     : https://prove2.me/submissions/d5225614-7ea8-458e-8d31-e5649e5e1031

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algebraMap_not_mem_map_of_colon_le_c246e15434f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_zero_of_socle_3e046c7b0432

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hR : SerreR B 1) (hS : SerreS B 2) {Q : Ideal B} (hQ : IsAssociatedPrime Q B) {q : B} (hq : q ∈ Q) :
    ∃ t ∉ Q, t * q = 0 := by
  obtain ⟨hprime, y, rfl⟩ := isAssociatedPrime_iff.mp hQ
  set Q := (⊥ : Submodule B B).colon {y} with hQdef
  have hmem : ∀ r, r ∈ Q ↔ r * y = 0 := fun r => by
    rw [hQdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  let L := Localization.AtPrime Q
  have hz : algebraMap B L y ≠ 0 := by
    have := algebraMap_not_mem_map_of_colon_le Q ⊥ (y := y) (fun r hr => (hmem r).mpr (by simpa using hr))
    simpa [Ideal.map_bot] using this
  have hk : ∀ m ∈ maximalIdeal L, m * algebraMap B L y = 0 := fun m hm => by
    have := mul_algebraMap_mem_map_of_le_colon Q ⊥ (y := y) (fun r hr => by simpa using (hmem r).mp hr) m hm
    simpa [Ideal.map_bot] using this
  have hdim := ringKrullDim_le_zero_of_socle (hS Q) hz hk
  have hreg : IsRegularLocalRing L := hR Q (hdim.trans (by decide))
  have hsf := (isRegularLocalRing_iff L).mp hreg
  have h0 : (maximalIdeal L).spanFinrank = 0 := by
    have : ((maximalIdeal L).spanFinrank : WithBot ℕ∞) ≤ 0 := hsf ▸ hdim
    exact Nat.le_zero.mp (by exact_mod_cast this)
  have hbot : maximalIdeal L = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal L).fg_of_isNoetherianRing).mp h0
  have hqm : algebraMap B L q ∈ maximalIdeal L := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L Q]
    exact hq
  rw [hbot, Submodule.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hqm
  obtain ⟨⟨t, ht⟩, htq⟩ := hqm
  exact ⟨t, ht, htq⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
