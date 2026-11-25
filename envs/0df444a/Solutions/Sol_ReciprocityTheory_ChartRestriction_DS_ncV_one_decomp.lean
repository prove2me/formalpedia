-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ncV_one_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:41.936526+00:00
-- url     : https://prove2.me/submissions/2bbd1c4c-25cf-405e-a44d-47e2426fd5bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp := by
  haveI : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hstab : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1 :=
    fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy
  let T : Module.End ℂ (ncV ε V 1) := (crossOp ε E 1 0).restrict hstab
  have hT : T.IsSymmetric := fun u v => crossOp_symm hU 1 0 u v
  have htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T μ := by
    rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun y : ncV ε V 1 => ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, (y : Big n 1 M) = xm + xp)
    hx' ?_ ⟨0, zero_mem _, 0, zero_mem _, by simp⟩ ?_
  · intro μ y hy
    by_cases hy0 : y = 0
    · exact ⟨0, zero_mem _, 0, zero_mem _, by simp [hy0]⟩
    have hTy : T y = μ • y := Module.End.mem_eigenspace_iff.1 hy
    have hev : Module.End.HasEigenvalue T μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
    have hμ : ((μ.re : ℝ) : ℂ) = μ := Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self hev)
    have hCy : crossOp ε E 1 0 y = ((μ.re : ℝ) : ℂ) • (y : Big n 1 M) := by
      rw [hμ]
      have := congrArg Subtype.val hTy
      simpa [T] using this
    have hyN : (y : Big n 1 M) ∈ Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1 :=
      ⟨Module.End.mem_eigenspace_iff.2 hCy, y.2⟩
    have hy0' : (y : Big n 1 M) ≠ 0 := fun h => hy0 (Subtype.ext h)
    rcases crossOp_eig_gap hE hU hV hmono hh hbig hyN hy0' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨0, zero_mem _, y, ?_, by simp⟩
      unfold Wp
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
    · refine ⟨y, ?_, 0, zero_mem _, by simp⟩
      unfold Wm
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
  · rintro y z ⟨a, ha, b, hb, hy⟩ ⟨c, hc, d, hd, hz⟩
    refine ⟨a + c, add_mem ha hc, b + d, add_mem hb hd, ?_⟩
    rw [Submodule.coe_add, hy, hz]
    abel
end ReciprocityTheory.ChartRestriction.DS
