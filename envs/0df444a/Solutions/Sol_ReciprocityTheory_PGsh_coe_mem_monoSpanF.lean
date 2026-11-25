-- Prove2me | solution 1 for ReciprocityTheory.PGsh.coe_mem_monoSpanF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:33.822742+00:00
-- url     : https://prove2.me/submissions/a8f9b92b-c762-4105-a158-265d50eecbf3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Theorems.Thm_ReciprocityTheory_PGsh_qExpansion_monoW_coeff_zero
import Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_nonempty
import Theorems.Thm_ReciprocityTheory_PGsh_mono_mem_monoSpanF
import Theorems.Thm_ReciprocityTheory_PGsh_mulDisc_mem

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
theorem _root_.solution (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.even_or_odd w with he | ho
  · by_cases h2 : w = 2
    · subst h2
      have : f = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f
      subst this
      simp
    obtain ⟨a, ha⟩ := monoIdx_nonempty he h2
    set g := f - (qExpansion 1 f).coeff 0 • monoW w a with hg
    have hgc : (qExpansion 1 g).coeff 0 = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
        (ModularForm.sub_smul_isCuspForm f _ (qExpansion_monoW_coeff_zero ha))
    have hfg : (⇑f : ℍ → ℂ) = ⇑g + (qExpansion 1 f).coeff 0 • ⇑(monoW w a) := by
      rw [hg]; simp
    rw [hfg]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (mono_mem_monoSpanF ha))
    by_cases h12 : w < 12
    · have h0 : ModularForm.toCuspForm g hgc = 0 :=
        rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
      have : (⇑g : ℍ → ℂ) = 0 := by
        funext z
        have := congrArg (fun F : CuspForm 𝒮ℒ (w : ℤ) => F z) h0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    · replace h12 : 12 ≤ w := by omega
      set h := CuspForm.discriminantEquiv (ModularForm.toCuspForm g hgc) with hh
      have hmem := ih (w - 12) (by omega) (ModularForm.mcast (by omega) h)
      have hgd : (⇑g : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑h := by
        have := ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hgc)
        rw [hh, this]; rfl
      rw [hgd]
      exact mulDisc_mem h12 hmem
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho.natCast) f
    subst this
    simp
end ReciprocityTheory.PGsh
