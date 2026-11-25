-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.ppos_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:04.733582+00:00
-- url     : https://prove2.me/submissions/4d680407-9123-462b-89b3-68c207d3f996

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
theorem _root_.solution {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by
  have hspan := hf τ
  have hmem : X.ppos z τ v ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z' τ) (Fin.castLE X.p0_le a)) := by
    rw [← hspan]
    unfold Data.ppos
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hβ]
  apply X.ppos_eq_of z' τ (X.gramPos_det_ne hz' τ) v β
  intro b
  rw [hβ]
  have hb : col (mat z' τ) (Fin.castLE X.p0_le b) ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) := by
    rw [hspan]; exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hb
  rw [← hγ, hermC_sum_right]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hermC_smul_right, X.ppos_orth z τ (X.gramPos_det_ne hz τ) v a, mul_zero]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
