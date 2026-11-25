-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.lattice_map_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:08.12797+00:00
-- url     : https://prove2.me/submissions/8aaa5f21-925a-4931-9382-acc9d2c6926e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SublatticeOfLattice
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : LatMap := by
  intro I x y γ g hγ hK u hu
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu ⊢
  have h1 : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      I.fmat γ.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    funext i
    rw [hγ]
    exact RingHom.map_mulVec _ _ _ i
  have hK' : ∀ v, v ∈ I.Lf ↔ I.fmat (x⁻¹ * γ * y).2 *ᵥ v ∈ I.Lf := hK
  have hk := (hK' (I.fmat y.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i))).1 hu
  rw [h1]
  convert hk using 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Formalism.MainNotions.S.AutInst.fmat, Prod.snd_mul, Prod.snd_inv]
  push_cast
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)),
    Matrix.mul_one]
end PI.UnitaryGroupMassFormula.LCG
