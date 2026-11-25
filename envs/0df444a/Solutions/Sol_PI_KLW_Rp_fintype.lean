-- Prove2me | solution 1 for PI.KLW.Rp_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:59.593851+00:00
-- url     : https://prove2.me/submissions/49ebd083-e50a-4fd2-8a01-db1a32d18863

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Theorems.Thm_PI_KLW_Rp_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW
theorem _root_.solution {α : Type} [Fintype α] (f : α → K) (h : ∀ z, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, h'⟩ := Rp_finset (p := p) Finset.univ f fun z _ => h z
  exact ⟨s, hs, fun z => h' z (Finset.mem_univ z)⟩
end PI.KLW
