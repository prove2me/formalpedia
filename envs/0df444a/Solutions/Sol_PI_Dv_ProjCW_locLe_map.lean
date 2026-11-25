-- Prove2me | solution 1 for PI.Dv.ProjCW.locLe_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:17.69273+00:00
-- url     : https://prove2.me/submissions/2f8437eb-2287-4b72-aadf-cb3c3e5356c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjCW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (M N : Submodule (𝓞 K) V)
    (f : V →ₗ[𝓞 K] V) (h : LocLe w F M N) : LocLe w F (M.map f) (N.map f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨s, hs, hsx⟩ := h x hx
  refine ⟨s, hs, ?_⟩
  rw [← map_smul, ← Submodule.map_smul'']
  exact Submodule.mem_map_of_mem hsx
end PI.Dv.ProjCW
