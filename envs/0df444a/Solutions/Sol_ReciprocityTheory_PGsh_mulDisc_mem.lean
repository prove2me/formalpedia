-- Prove2me | solution 1 for ReciprocityTheory.PGsh.mulDisc_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:54.250427+00:00
-- url     : https://prove2.me/submissions/25c7b664-9b7b-45c5-b63c-25d4759faea7

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_wt
import Theorems.Thm_ReciprocityTheory_PGsh_coe_monoW
import Theorems.Thm_ReciprocityTheory_PGsh_mono_mem_monoSpanF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries
namespace ReciprocityTheory.PGsh
theorem _root_.solution {w : ℕ} (hw : 12 ≤ w) {φ : ℍ → ℂ} (hφ : φ ∈ monoSpanF (w - 12)) :
    (ModularForm.discriminant : ℍ → ℂ) * φ ∈ monoSpanF w := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    have hwt := monoIdx_wt ha
    have ha3 : a + 3 ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a, by omega⟩⟩
    have ha0 : a ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a + 2, by omega⟩⟩
    have hb3 : monoB w (a + 3) = monoB (w - 12) a := by
      have := monoIdx_wt ha3; omega
    have hb0 : monoB w a = monoB (w - 12) a + 2 := by
      have := monoIdx_wt ha0; omega
    have heq : (ModularForm.discriminant : ℍ → ℂ) * ⇑(monoW (w - 12) a) =
        (1728 : ℂ)⁻¹ • ((⇑(monoW w (a + 3)) : ℍ → ℂ) - ⇑(monoW w a)) := by
      rw [coe_monoW ha, coe_monoW ha3, coe_monoW ha0, hb3, hb0]
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mono_mem_monoSpanF ha3)
      (mono_mem_monoSpanF ha0))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
end ReciprocityTheory.PGsh
