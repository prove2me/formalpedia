-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Wp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:37.94284+00:00
-- url     : https://prove2.me/submissions/d93ecbd8-9dfd-4c1c-ad86-22899f55e53d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_eig_gap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_crossOp_eig_eq_zero


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
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
  have key : ∀ s : Finset ℝ, ∀ x ∈ ⨆ θ ∈ s, ⨆ (_ : 0 < θ),
      Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1,
      (h - n + 1) * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; simp at hx; simp [hx]
    | insert a s has ih =>
      intro x hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      by_cases ha : 0 < a
      · rw [iSup_pos ha] at hy
        have hCy : crossOp ε E 1 0 y = (a : ℂ) • y := Module.End.mem_eigenspace_iff.1 hy.1
        have horth : inner ℂ y z = 0 := by
          have hle : (⨆ θ ∈ s, ⨆ (_ : 0 < θ),
              Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ (ℂ ∙ y)ᗮ := by
            refine iSup₂_le (fun θ hθ => iSup_le (fun _ => ?_))
            intro w hw
            rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
            exact inner_crossOp_eig_eq_zero hU (by rintro rfl; exact has hθ) hCy
              (Module.End.mem_eigenspace_iff.1 hw.1)
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)
        have horth' : inner ℂ z y = 0 := by rw [inner_eq_zero_symm]; exact horth
        have hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
          have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z horth
          rw [sq, sq, sq]; exact this
        have h1 : inner ℂ (crossOp ε E 1 0 z) y = 0 := by
          rw [crossOp_symm hU, hCy, inner_smul_right, horth', mul_zero]
        have hre : RCLike.re (inner ℂ (crossOp ε E 1 0 (y + z)) (y + z)) =
            a * ‖y‖ ^ 2 + RCLike.re (inner ℂ (crossOp ε E 1 0 z) z) := by
          rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, hCy, inner_smul_left,
            inner_smul_left, horth, inner_self_eq_norm_sq_to_K]
          simp
          left
          norm_cast
        have hy' : (h - n + 1) * ‖y‖ ^ 2 ≤ a * ‖y‖ ^ 2 := by
          by_cases hy0 : y = 0
          · simp [hy0]
          · rcases crossOp_eig_gap hE hU hV hmono hh hbig hy hy0 with ⟨-, h2⟩ | ⟨h2, h3⟩
            · exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
            · exfalso; linarith
        rw [hnorm, hre]
        nlinarith [ih z hz, hy']
      · rw [iSup_neg ha] at hy
        rw [(Submodule.mem_bot ℂ).1 hy, zero_add]
        exact ih z hz
  unfold Wp at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  have := key s x hs
  linarith
end ReciprocityTheory.ChartRestriction.DS
