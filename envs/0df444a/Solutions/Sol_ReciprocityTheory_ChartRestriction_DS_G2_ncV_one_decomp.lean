-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.G2.ncV_one_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:27.839102+00:00
-- url     : https://prove2.me/submissions/18d31f1c-744d-47f6-9012-fcaa6dba2ae6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_NcVOneDecomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_G2_crossOp_eig_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_eig_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_mem_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_ncV


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.G2
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp := by
  classical
  have hinv : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1 :=
    fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy
  haveI : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  let T' : Module.End ℂ (ncV ε V 1) := (crossOp ε E 1 0).restrict hinv
  have hT' : T'.IsSymmetric := fun u v => crossOp_symm hU 1 0 u v
  have htop : (⨆ μ, Module.End.eigenspace T' μ) = ⊤ := by
    have := hT'.orthogonalComplement_iSup_eigenspaces_eq_bot
    rwa [Submodule.orthogonal_eq_bot_iff] at this
  have hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T' μ := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨g, hg, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have hreal : ∀ μ, g μ ≠ 0 → μ = ((μ.re : ℝ) : ℂ) := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue T' μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hg μ, hμ⟩
    exact (Complex.conj_eq_iff_re.1 (hT'.conj_eigenvalue_eq_self hev)).symm
  have hmem : ∀ μ, ((g μ : ncV ε V 1) : Big n 1 M) ∈
      Module.End.eigenspace (crossOp ε E 1 0) μ ⊓ ncV ε V 1 := by
    intro μ
    refine Submodule.mem_inf.2 ⟨?_, (g μ).2⟩
    rw [Module.End.mem_eigenspace_iff]
    exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 (hg μ))
  have hmem' : ∀ μ, g μ ≠ 0 → ((g μ : ncV ε V 1) : Big n 1 M) ∈
      Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1 := by
    intro μ hμ
    have h1 := hmem μ
    rwa [← hreal μ hμ]
  have hne : ∀ μ, g μ ≠ 0 → ((g μ : ncV ε V 1) : Big n 1 M) ≠ 0 := by
    intro μ hμ h0
    exact hμ (Subtype.ext h0)
  have hxsum : x = ∑ μ ∈ g.support, ((g μ : ncV ε V 1) : Big n 1 M) := by
    have := congrArg Subtype.val hsum
    simpa [Finsupp.sum] using this.symm
  refine ⟨∑ μ ∈ g.support.filter (fun μ => μ.re < 0), ((g μ : ncV ε V 1) : Big n 1 M), ?_,
    ∑ μ ∈ g.support.filter (fun μ => ¬ μ.re < 0), ((g μ : ncV ε V 1) : Big n 1 M), ?_, ?_⟩
  · show _ ∈ ⨆ (θ : ℝ) (_ : θ < 0), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
    refine Submodule.sum_mem _ fun μ hμ => ?_
    by_cases h0 : g μ = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem μ.re
        (Submodule.mem_iSup_of_mem (Finset.mem_filter.1 hμ).2 (hmem' μ h0))
  · show _ ∈ ⨆ (θ : ℝ) (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
    refine Submodule.sum_mem _ fun μ hμ => ?_
    by_cases h0 : g μ = 0
    · rw [h0]; exact Submodule.zero_mem _
    · have hnn : ¬ μ.re < 0 := (Finset.mem_filter.1 hμ).2
      have hpos : 0 < μ.re := by
        rcases crossOp_eig_gap hE hU hV hmono hh hbig (hmem' μ h0) (hne μ h0) with h1 | h1
        · linarith [h1.1, h1.2]
        · exact absurd (by linarith [h1.1, h1.2]) hnn
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem hpos (hmem' μ h0))
  · rw [Finset.sum_filter_add_sum_filter_not]
    exact hxsum
end ReciprocityTheory.ChartRestriction.DS.G2
