-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_MultigradedFiltration_equiv_mp_95fd47e08066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:22.793553+00:00
-- url     : https://prove2.me/submissions/52db6f49-5547-4466-a64c-1c9c1a6579b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_span_image_val_lt_succ_acfa6b6fbf75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_isMultigraded_iff_isMultigrading_ac258fa1b81e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
namespace MultigradedFiltration
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement.{u, u} →
      MultigradedFiltration.Statement.{u} := by
  intro hA F _ K _ _ ι _ M _ _ _ _ ℳ hℳ hfin
  have := hfin
  obtain ⟨n, N, x, c, q, hN0, hNl, hj, -⟩ :=
    hA F K ι M ℳ ((isMultigraded_iff_isMultigrading ℳ).mp hℳ)
  have hNspan : ∀ (k : ℕ) (hk : k < n + 1),
      N ⟨k, hk⟩ = Submodule.span (MRing ι F) (x '' {i | i.val < k}) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, hN0]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hs := (hj ⟨k, hkn⟩).2.1
      have e1 : (⟨k, hkn⟩ : Fin n).succ = ⟨k + 1, hk⟩ := rfl
      have e2 : (⟨k, hkn⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
      rw [e1, e2] at hs
      rw [hs, ih (by omega)]
      exact (span_image_val_lt_succ x ⟨k, hkn⟩).symm
  refine ⟨n, x, c, q, fun j => (hj j).1, fun j => ⟨(hj j).2.2.1, (hj j).2.2.2.1⟩, ?_, ?_⟩
  · have h := hNspan n (by omega)
    have e : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [e, hNl] at h
    rw [h, ← Set.image_univ]
    congr 2
    ext i
    simp
  · intro j f
    have h := (hj j).2.2.2.2 f
    have e : j.castSucc = ⟨j.val, by omega⟩ := rfl
    rw [e, hNspan j.val (by omega)] at h
    exact h
end MultigradedFiltration
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
