-- Prove2me | solution 1 for P2M_PI_FinKW_smul_one_tmul__5e47ee373b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:47.902486+00:00
-- url     : https://prove2.me/submissions/782eb793-5e5f-4a71-a129-e06029569a44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : v.adicCompletionIntegers I.F)
    (e : I.E) :
    r • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] e) = ((r : v.adicCompletion I.F) ⊗ₜ[I.F] e) := by
  rw [TensorProduct.smul_tmul']
  congr 1
  rw [Algebra.smul_def, mul_one]
  rfl
end PI.FinKW
