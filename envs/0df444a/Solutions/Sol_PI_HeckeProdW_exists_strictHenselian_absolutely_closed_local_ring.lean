-- Prove2me | solution 1 for PI.HeckeProdW.exists_strictHenselian_absolutely_closed_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:48.16075+00:00
-- url     : https://prove2.me/submissions/c484bbb9-78a9-4cc1-a233-b9f101215867

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Theorems.Thm_PI_HeckeProdW_no_small
import Theorems.Thm_PI_HeckeProdW_Phi_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]
variable {L}
namespace PI.HeckeProdW
theorem _root_.solution (χ : HChar L) : ∃ T : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ y : Pu L, (∀ v ∈ T, y v = 1) → χ.1 (Phi L y) = 1 := by
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2} with hWdef
  have hW : IsOpen W :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hc : Continuous (fun y => χ.1 (Phi L y)) := χ.2.1.comp (Phi_cont L)
  have h1 : (fun y => χ.1 (Phi L y)) 1 ∈ W := by
    simp only [map_one, hWdef, Set.mem_setOf_eq, Units.val_one, sub_self, norm_zero]
    norm_num
  have hmem : (fun y => χ.1 (Phi L y)) ⁻¹' W ∈ 𝓝 (1 : Pu L) :=
    hc.continuousAt.preimage_mem_nhds (hW.mem_nhds h1)
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := hmem
  refine ⟨hI.toFinset, fun y hy => ?_⟩
  have hyI : ∀ n : ℕ, y ^ n ∈ I.pi t := by
    intro n i hi
    rw [Pi.pow_apply, hy i (hI.mem_toFinset.2 hi), one_pow]
    exact mem_of_mem_nhds (ht i)
  refine Units.ext (no_small _ fun n => ?_)
  have h2 := hsub (hyI n)
  simp only [Set.mem_preimage, map_pow, hWdef, Set.mem_setOf_eq, Units.val_pow_eq_pow_val] at h2
  exact h2
end PI.HeckeProdW
