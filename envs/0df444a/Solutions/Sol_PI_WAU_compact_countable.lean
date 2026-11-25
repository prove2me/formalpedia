-- Prove2me | solution 1 for PI.WAU.compact_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:31.891197+00:00
-- url     : https://prove2.me/submissions/dfbf97e5-0e9a-4862-a529-cdbee3938658

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Theorems.Thm_PI_WAU_B_cover_of
import Theorems.Thm_PI_WAU_B_step
import Theorems.Thm_PI_WAU_B_exists_PN
import Theorems.Thm_PI_WAU_B_countable_cls
import Theorems.Thm_PI_WAU_B_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open PI.WAU.B
namespace PI.WAU
theorem _root_.solution : KCountable := by
  intro I
  obtain ⟨k, m, hm, hgen⟩ := exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  have hcov : ∀ N : ℕ, ∃ s : Set I.Gf, s.Countable ∧
      ∀ x, PN I m N x → ∃ y ∈ s, y⁻¹ * x ∈ I.Kset := by
    intro N
    haveI : Countable (Bad I.F (N * N) → I.F) := countable_cls (N * N)
    exact cover_of I.Kset (PN I m N) (fN I m N) fun x y hx hy he => step I m hm hgen hx hy he
  choose s hs hsK using hcov
  refine ⟨⋃ N, s N, Set.countable_iUnion hs, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_PN I m x
  obtain ⟨y, hy, hyK⟩ := hsK N x hN
  exact ⟨y, Set.mem_iUnion.mpr ⟨N, hy⟩, hyK⟩
end PI.WAU
