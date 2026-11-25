-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_MultigradedFiltration_equiv_mpr_0dafaa7127e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:55.310165+00:00
-- url     : https://prove2.me/submissions/5bd2c70a-f33f-4c8e-863f-556f132e3046

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb
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
    MultigradedFiltration.Statement.{u} →
      GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement.{u, u} := by
  intro hB F _ K _ _ ι _ M _ _ _ _ _ piece hpiece
  obtain ⟨n, x, c, q, hx, hq, hspan, hann⟩ :=
    hB F K ι M piece ((isMultigraded_iff_isMultigrading piece).mpr hpiece) inferInstance
  let N : Fin (n + 1) → Submodule (MRing ι F) M := fun k =>
    Submodule.span (MRing ι F) (x '' {i | i.val < k.val})
  have hN0 : N 0 = ⊥ := by simp [N]
  have hNl : N (Fin.last n) = ⊤ := by
    simp only [N, Fin.val_last]
    rw [← hspan, ← Set.image_univ]
    congr 2
    ext i
    simp
  have hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} := by
    intro j
    simp only [N, Fin.val_succ, Fin.val_castSucc]
    exact span_image_val_lt_succ x j
  have hann' : ∀ j (s : MRing ι F), s • x j ∈ N j.castSucc ↔ s ∈ q j := fun j s => hann j s
  refine ⟨n, N, x, c, q, hN0, hNl, fun j => ⟨hx j, hsucc j, (hq j).1, (hq j).2, hann' j⟩, ?_⟩
  intro W hW
  have : W.IsPrime := hW.1.1
  classical
  convert card_eq_length_of_filtration N x q hN0 hNl hsucc (fun j => (hq j).1) hann' W hW using 1
  rfl
end MultigradedFiltration
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
