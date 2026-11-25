-- Prove2me | solution 1 for PI.Residue.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:06.0725+00:00
-- url     : https://prove2.me/submissions/68f469cd-f793-481e-8495-8cdf2ad3979a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_PI_Residue_mem_lat
import Theorems.Thm_PI_Residue_smul_mem_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (hx : x ∈ lat K J) (hx0 : x ≠ 0) :
    ∃ x1 ∈ idealSet K J, ∃ g : (𝓞 K)ˣ ⧸ torsion K, urep g • x1 = x := by
  have hnx : mixedEmbedding.norm x ≠ 0 := by
    obtain ⟨a, _, rfl⟩ := mem_lat.1 hx
    exact fun h => hx0 ((norm_eq_zero_iff' ⟨_, rfl⟩).1 h)
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hnx
  obtain ⟨ζ, hζ⟩ := QuotientGroup.mk_out_eq_mul (torsion K) u⁻¹
  have hζ' : (ζ : (𝓞 K)ˣ)⁻¹ ∈ torsion K := inv_mem ζ.2
  refine ⟨(ζ : (𝓞 K)ˣ)⁻¹ • (u • x), ⟨torsion_smul_mem_of_mem hu hζ',
    smul_mem_lat _ (smul_mem_lat _ hx)⟩, QuotientGroup.mk u⁻¹, ?_⟩
  rw [urep, hζ, ← mul_smul, ← mul_smul]
  simp
end PI.Residue
