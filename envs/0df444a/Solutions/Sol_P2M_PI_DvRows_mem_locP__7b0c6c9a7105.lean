-- Prove2me | solution 1 for P2M_PI_DvRows_mem_locP__7b0c6c9a7105
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:18.991344+00:00
-- url     : https://prove2.me/submissions/839f1c32-f1b2-4d61-b49f-46451b8fbe0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
namespace PI.DvRows
theorem _root_.solution (p : Ideal R) [p.IsPrime] {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl
end PI.DvRows
