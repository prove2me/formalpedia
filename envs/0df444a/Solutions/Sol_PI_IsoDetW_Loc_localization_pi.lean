-- Prove2me | solution 1 for PI.IsoDetW.Loc.localization_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:50.12898+00:00
-- url     : https://prove2.me/submissions/3503e5fb-7b5e-4e1c-9287-8670cf9ce805

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Theorems.Thm_PI_IsoDetW_Loc_mem_locP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
namespace PI.IsoDetW.Loc
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : Ideal R) [p.IsPrime]
    (X : ∀ i, Submodule R (M i)) :
    localization₂ p (Submodule.pi Set.univ X) = Submodule.pi Set.univ (fun i => localization₂ p (X i)) := by
  classical
  ext x
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_locP]
  constructor
  · rintro ⟨s, hs, hsx⟩ i
    exact ⟨s, hs, by simpa using hsx i⟩
  · intro h
    choose s hs hsx using h
    refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, fun i => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Pi.smul_apply, mul_smul]
    exact (X i).smul_mem _ (hsx i)
end PI.IsoDetW.Loc
