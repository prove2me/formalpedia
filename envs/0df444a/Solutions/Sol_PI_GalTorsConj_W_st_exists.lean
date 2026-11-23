-- Prove2me | solution 1 for PI.GalTorsConj.W.st_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:59.255543+00:00
-- url     : https://prove2.me/submissions/918162ec-bb09-4516-916e-55e676b795c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution (hO : POnto) (hg2 : L.g₂ ∈ M) (hg3 : L.g₃ ∈ M)
    (hg2' : L'.g₂ = ρ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ ⟨_, hg3⟩) (t : ℂ)
    (ht : t ∈ L.lattice ∨ (L.weierstrassP t ∈ M ∧ L.derivWeierstrassP t ∈ M)) :
    ∃ t', St L L' M ρ t t' := by
  by_cases h : t ∈ L.lattice
  · exact ⟨0, Or.inl ⟨h, L'.lattice.zero_mem⟩⟩
  obtain ⟨hx, hy⟩ := ht.resolve_left h
  set X : M := ⟨_, hx⟩
  set Y : M := ⟨_, hy⟩
  have curve : Y ^ 2 = 4 * X ^ 3 - ⟨_, hg2⟩ * X - ⟨_, hg3⟩ :=
    Subtype.ext (by
      have e := L.derivWeierstrassP_sq t h
      have h4 : ((4 : M) : ℂ) = 4 := map_ofNat (algebraMap M ℂ) 4
      push_cast [X, Y, h4]
      linear_combination e)
  have curve' : (ρ Y) ^ 2 = 4 * (ρ X) ^ 3 - L'.g₂ * ρ X - L'.g₃ := by
    rw [hg2', hg3']
    have := congrArg ρ curve
    simpa [map_sub, map_mul, map_pow, map_ofNat] using this
  obtain ⟨z, hz, e1, e2⟩ := hO L' (ρ X) (ρ Y) curve'
  exact ⟨z, Or.inr ⟨h, hz, hx, hy, e1, e2⟩⟩
end PI.GalTorsConj.W
