-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_gt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:26.13368+00:00
-- url     : https://prove2.me/submissions/3f29efe2-c248-4b21-9323-ca73ac592e2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_rho_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_rho_surj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_SSZ_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_mono_split

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
theorem _root_.solution {K : Type*} [Field K] : ∀ (k : ℕ) (κ : Fin k → ℤ), (∀ s, 0 ≤ κ s) →
    ∀ [Fintype (sq_SSZ k κ)] (t : Fin k → K), ∑ g : sq_SSZ k κ, sq_mono t g.1 = gtChar k κ t := by
  intro k
  induction k with
  | zero =>
    intro κ _ _ t
    have : Unique (sq_SSZ 0 κ) :=
      { default := ⟨fun a => a.elim0, fun l => l.elim0, fun s => s.elim0⟩
        uniq := fun g => Subtype.ext (funext fun a => a.elim0) }
    rw [Fintype.sum_unique]
    simp [sq_mono, gtChar]
  | succ k ih =>
    intro μ hμ _ t
    have : ∀ κ : Fin k → ℤ, Fintype (sq_SSZ k κ) := fun κ => @Fintype.ofFinite _ (sq_SSZ_finite k κ)
    have : Fintype (sq_UU k μ) := Fintype.ofEquiv _ (sq_fibEquiv μ).symm
    rw [Fintype.sum_bijective (sq_rho μ) ⟨sq_rho_inj μ, sq_rho_surj μ (hμ _)⟩ _
      (fun u : sq_UU k μ => sq_mono (fun i => t i.castSucc) u.1 *
        t (Fin.last k) ^ (wsum μ - wsum (fun s => ((∑ a, u.1 a s : ℕ) : ℤ)))) (sq_mono_split μ t)]
    refine (Fintype.sum_equiv (sq_fibEquiv μ) _
      (fun x : (Σ κ : ↥(interl μ), sq_SSZ k κ.1) => sq_mono (fun i => t i.castSucc) x.2.1 *
        t (Fin.last k) ^ (wsum μ - wsum x.1.1)) (fun u => rfl)).trans ?_
    rw [Fintype.sum_sigma]
    simp only [← Finset.sum_mul]
    rw [gtChar, ← Finset.sum_coe_sort (interl μ)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [ih κ.1 (fun s => le_trans (hμ _) ((sq_mem_interl μ κ.1).1 κ.2 s).1)]
end ReciprocityTheory.ChartRestriction.TR.Weyl
