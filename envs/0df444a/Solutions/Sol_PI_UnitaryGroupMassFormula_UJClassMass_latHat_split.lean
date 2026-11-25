-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.latHat_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:27.127687+00:00
-- url     : https://prove2.me/submissions/6d2b7ef9-e5a9-4e56-a684-0d615e05cd4d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Oh_smul_latHat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (L : Set (Fin M → E)) (hL : ∀ e : E, IsIntegral ℤ e → ∀ x ∈ L, e • x ∈ L)
    (f : ι → Af F ⊗[F] E) (hf : ∀ i j, f i * f j = if i = j then f i else 0)
    (hO : ∀ i, f i ∈ PI.UnitaryGroupMassFormula.UJClassFin.Oh F E) (y : ι → Fin M → Af F ⊗[F] E) :
    ∑ i, f i • y i ∈ latHat F E L ↔ ∀ i, f i • y i ∈ latHat F E L := by
  constructor
  · intro h j
    have h1 := Oh_smul_latHat L hL (hO j) h
    have e : f j • ∑ i, f i • y i = f j • y j := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hf j, ite_smul, zero_smul]
      simp
    rwa [e] at h1
  · intro h
    exact AddSubgroup.sum_mem _ (fun i _ => h i)
end PI.UnitaryGroupMassFormula.UJClassMass
