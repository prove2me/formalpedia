-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:51.398299+00:00
-- url     : https://prove2.me/submissions/498da1fe-0b97-48ea-8a4e-cf20e886fb04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)
set_option maxHeartbeats 2000000
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : d.u * fb d 1 1 = 1 := by
  have heq : (PiTensorProduct.tprod Ω (fun _ : Unit => exteriorPower.ιMulti Ω 1
      (fun a : Fin 1 => lineF.mkQ ((Pi.basisFun Ω (Fin 2)) (tailIdx (show 1 ≤ 2 by decide) a)))) :
        PiTensorProduct Ω (fun _ : Unit => ⋀[Ω]^1 ((Fin 2 → Ω) ⧸ lineF))) =
      (d.u * chartMono yLine d.c 0) • PiTensorProduct.tprod Ω (fun _ : Unit => exteriorPower.ιMulti Ω 1
        (fun a : Fin 1 => lineF.mkQ (d.b () (tailIdx (show 1 ≤ 2 by decide) a)))) := d.eq
  have e1 := congrArg (PiTensorProduct.subsingletonEquiv (R := Ω)
    (s := fun _ : Unit => ⋀[Ω]^1 ((Fin 2 → Ω) ⧸ lineF)) ()) heq
  rw [LinearEquiv.map_smul] at e1
  simp only [PiTensorProduct.subsingletonEquiv_apply_tprod] at e1
  have e2 := congrArg (exteriorPower.oneEquiv Ω ((Fin 2 → Ω) ⧸ lineF)) e1
  simp only [map_smul, exteriorPower.oneEquiv_ιMulti, chartMono, Finset.univ_unique,
    Finset.prod_singleton] at e2
  have ht' : ∀ (h : 1 ≤ 2) (a : Fin (2 - 1)), tailIdx h a = 1 := fun _ a => Fin.ext (by
    have := a.isLt
    simp only [tailIdx, Fin.val_one]
    omega)
  simp only [ht', Pi.basisFun_apply, Pi.zero_apply, zpow_zero, mul_one, Submodule.mkQ_apply,
    ← Submodule.Quotient.mk_smul] at e2
  have e3 := (Submodule.Quotient.eq lineF).1 e2
  have := mem_lineF_apply_one e3
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
  exact (sub_eq_zero.1 this).symm
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
