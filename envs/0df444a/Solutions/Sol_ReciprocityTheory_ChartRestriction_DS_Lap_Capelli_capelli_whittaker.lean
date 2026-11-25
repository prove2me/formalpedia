-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_whittaker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:40.940174+00:00
-- url     : https://prove2.me/submissions/28b76888-85ef-4dd5-b7ad-4130e0e1f17b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_seg_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_cminor_cast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_kappa
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_phase1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_phase2a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_phase2b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_intertwine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ)
    (l : M →ₗ[ℂ] R) (x : ℂ) (hE : IsGlRep E) (hr : 0 < r)
    (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
    (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
    (hD : ∀ i j, l ∘ₗ E (wIdx k r i) (wIdx k r j) = D i j ∘ₗ l) :
    l ∘ₗ cminor E Fin.castSucc Fin.succ x =
      ((-1) ^ k * kappa k r ψ) • (capelliC D (x - (r : ℂ)) ∘ₗ l) := by
  have hb : 0 + (k + 2 * r) ≤ k + 2 * r + 1 := by omega
  have hb' : 1 + (k + 2 * r) ≤ k + 2 * r + 1 := by omega
  have h1 : (Fin.castSucc : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) =
      whB_seg (k + 2 * r + 1) 0 (k + 2 * r) := by
    funext i; apply Fin.ext; rw [whB_seg_val hb]; simp
  have h2 : (Fin.succ : Fin (k + 2 * r) → Fin (k + 2 * r + 1)) =
      whB_seg (k + 2 * r + 1) 1 (k + 2 * r) := by
    funext i; apply Fin.ext; rw [whB_seg_val hb']; simp; ring
  have hW : whB_seg (k + 2 * r + 1) r k = wIdx k r ∘ id := by
    funext i; apply Fin.ext; rw [whB_seg_val (by omega)]; rfl
  have hinj : Function.Injective (wIdx k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [wIdx] at this; exact this
  rw [h1, h2, whB_cminor_cast E (show k + 2 * r = k + r + r by ring) rfl rfl x,
    whB_phase1 k r E ψ l hE hl hψ r le_rfl x,
    whB_cminor_cast E (show k + r = k + (r - 1) + 1 by omega) rfl (show 1 = 0 + 1 from rfl) (x - r),
    whB_phase2a k r E ψ l hE hl hψ (r - 1) 0 (by omega) (x - r),
    whB_phase2b k r E ψ l hE hl hψ hr (x - r), hW,
    cminor_intertwine E D (wIdx k r) hinj l hD id id (x - r), smul_smul, smul_smul, whB_kappa k r hr ψ]
  congr 1; ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
