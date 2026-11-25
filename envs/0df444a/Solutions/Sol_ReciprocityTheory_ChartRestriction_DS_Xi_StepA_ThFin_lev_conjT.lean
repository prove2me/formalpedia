-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin.lev_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:03.170216+00:00
-- url     : https://prove2.me/submissions/1fc8685a-6189-4b32-8465-33d74e54ad32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos


section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ThFin
private lemma conjTranspose_Hpk_eq_Hpk (k r' : ℕ) : (Hpk k r')ᴴ = Hpk k r' := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | rfl | norm_num
end ThFin
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
theorem _root_.solution (k r' : ℕ) : (ιLev k 1 r' (Hpk k r'))ᴴ = ιLev k 1 r' (Hpk k r') := by
  have hc := conjTranspose_Hpk_eq_Hpk k r'
  ext p q
  rw [Matrix.conjTranspose_apply]
  unfold ιLev
  try dsimp only
  split_ifs <;> first | ((conv_rhs => rw [← hc]); rfl) | (simp; done) | (subst_vars; contradiction)
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ThFin
