-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.matV_listProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:04.571974+00:00
-- url     : https://prove2.me/submissions/24c8aa0e-edaa-48a2-aa62-984b12af9fdb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
open Classical
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution (I : AutInst) (loc : ∀ v, GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (Y : HeightOneSpectrum (𝓞 I.F) → I.Gf)
    (hY1 : ∀ v, matV I v (Y v : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = loc v)
    (hY2 : ∀ v, SuppAt I v (Y v)) (l : List (HeightOneSpectrum (𝓞 I.F))) (hl : l.Nodup)
    (w : HeightOneSpectrum (𝓞 I.F)) :
    matV I w (((l.map Y).prod : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      if w ∈ l then loc w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, map_mul, ih hl.2]
    by_cases hw : w = v
    · subst hw
      simp [hY1, hl.1]
    · rw [hY2 v w hw]
      simp [hw]
end PI.UnitaryGroupMassFormula.ScXuExists.Gl
