-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.orthogonal_lattice_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:52.231944+00:00
-- url     : https://prove2.me/submissions/0173ef8b-2f84-41f3-9c91-de11a261cbe5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_iso_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jz_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : ProjectionAlongComplement (E := E) := by
  intro r X ξ hξ x hx u hu
  obtain ⟨-, hiso, hne⟩ := hξ
  have key : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.ucomp x ξ u τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.Jz x (X.ucomp x ξ u) τ) (Data.emb τ.1 ξ) = 0 := by
    intro τ
    set e := Data.emb τ.1 ξ with he
    have he0 : e ≠ 0 := emb_ne_zero τ.1 hne
    have hee : hermC τ.1 X.Gm e e = 0 := by rw [he, hermC_emb, hiso, map_zero]
    have hη : X.Hf x τ e e ≠ 0 := fun h => by
      have := X.Hf_iso_pos hx τ he0 hee
      rw [h] at this; simp at this
    have hu' : X.ucomp x ξ u τ = u τ - (X.Hf x τ (u τ) e / X.Hf x τ e e) • e := rfl
    refine ⟨?_, ?_⟩
    · rw [hu', hermC_sub_left, hermC_smul_left, hee, mul_zero, sub_zero]
      exact hu τ
    · rw [Data.Jz_apply, hu', hermC_smul_left, Data.jp_sub, Data.jp_smul, hermC_sub_left,
        hermC_smul_left, ← Data.Hf_eq_jp, ← Data.Hf_eq_jp, div_mul_cancel₀ _ hη, sub_self, mul_zero]
  exact ⟨fun τ => (key τ).1, fun τ => (key τ).2⟩
end ReciprocityTheory.ChartRestriction.G.FD
