-- Prove2me | solution 1 for PI.VolStabW.IdxHW.val_of_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:08.433329+00:00
-- url     : https://prove2.me/submissions/8a41c728-c7d8-4655-8f26-b8dc5f4afc93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Theorems.Thm_ReciprocityTheory_Aut_mem_maxIdeal_iff
import Theorems.Thm_ReciprocityTheory_Aut_val_le_exp_neg_one_of_lt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution (x : v.adicCompletionIntegers F) (h : residue _ x = 0) :
    Valued.v (x : Fv F v) ≤ WithZero.exp (-1 : ℤ) :=
  ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v
    ((ReciprocityTheory.Aut.mem_maxIdeal_iff v x).1 ((residue_eq_zero_iff x).1 h))
end PI.VolStabW.IdxHW
