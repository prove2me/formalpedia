-- Prove2me | solution 1 for ReciprocityTheory.CA.ModDepthGE.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:33.467827+00:00
-- url     : https://prove2.me/submissions/aa686dab-2662-4b35-9a18-d4c7eb8943a7

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace ModDepthGE
theorem _root_.solution {m n : ℕ} (hmn : m ≤ n) (h : ModDepthGE R M n) : ModDepthGE R M m := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.take m, by simp [hlen, hmn], fun r hr => hmem r (List.mem_of_mem_take hr), ?_⟩
  have hw : IsWeaklyRegular M (rs.take m) := by
    have := hreg.toIsWeaklyRegular
    rw [← List.take_append_drop m rs, isWeaklyRegular_append_iff] at this
    exact this.1
  refine ⟨hw, fun htop => hreg.top_ne_smul ?_⟩
  refine le_antisymm (htop.le.trans (Submodule.smul_mono_left ?_)) le_top
  exact Ideal.span_mono fun r hr => List.mem_of_mem_take hr
end ModDepthGE
end ReciprocityTheory.CA
