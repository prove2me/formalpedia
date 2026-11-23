-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:29.986713+00:00
-- url     : https://prove2.me/submissions/5d221910-669c-4f9d-97b4-723872675d5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idx_eq_zero_of_loc
import Theorems.Thm_PI_Dv_ProjGramW_locLe_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X : Submodule (𝓞 K) V} (hX : X.FG) :
    idxAt w X X = 0 := by
  have hl : LocLe w 0 X X := (locLe_zero_iff w X X).mpr fun x hx =>
    ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [one_smul]; exact hx⟩
  exact idx_eq_zero_of_loc hI w hX hX hl hl
end PI.Dv.ProjGramW
