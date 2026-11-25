-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_mono_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:04.751723+00:00
-- url     : https://prove2.me/submissions/e6000d9a-9251-40e4-b3b1-1ce62b702187

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_intl_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] {k : ℕ} (μ : Fin (k + 1) → ℤ) (t : Fin (k + 1) → K)
    (g : sq_SSZ (k + 1) μ) :
    sq_mono t g.1 = sq_mono (fun i => t i.castSucc) (sq_restr g.1) *
      t (Fin.last k) ^ (wsum μ - wsum (fun s => ((∑ a, sq_restr g.1 a s : ℕ) : ℤ))) := by
  obtain ⟨g, hI, hs⟩ := g
  have hrow : ∀ a : Fin k, sq_rowSum g a.castSucc = sq_rowSum (sq_restr g) a := by
    intro a
    rw [sq_rowSum, Fin.sum_univ_castSucc,
      sq_intl_zero g hI k (Fin.last k) rfl a.castSucc (by simp), add_zero]
    rfl
  have hlast : ((sq_rowSum g (Fin.last k) : ℕ) : ℤ) =
      wsum μ - wsum (fun s => ((∑ a, sq_restr g a s : ℕ) : ℤ)) := by
    have h1 : wsum μ = ∑ a, (sq_rowSum g a : ℤ) := by
      simp only [wsum, ← hs, sq_rowSum]
      push_cast
      exact Finset.sum_comm
    have h2 : wsum (fun s => ((∑ a, sq_restr g a s : ℕ) : ℤ)) =
        ∑ a : Fin k, (sq_rowSum (sq_restr g) a : ℤ) := by
      simp only [wsum, sq_rowSum]
      push_cast
      exact Finset.sum_comm
    rw [h1, h2, Fin.sum_univ_castSucc]
    simp only [hrow]
    ring
  simp only [sq_mono]
  rw [Fin.prod_univ_castSucc, ← hlast, zpow_natCast]
  simp only [hrow]
end ReciprocityTheory.ChartRestriction.TR.Weyl
