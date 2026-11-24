-- Prove2me | solution 1 for PI.WAU.ohat_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:27.138732+00:00
-- url     : https://prove2.me/submissions/b607f93c-c6e0-4e65-96cd-37286e5e0583

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Theorems.Thm_PI_WAU_ohat_add
import Theorems.Thm_PI_WAU_ohat_zero

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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU
theorem _root_.solution {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ohat_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ohat_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end PI.WAU
