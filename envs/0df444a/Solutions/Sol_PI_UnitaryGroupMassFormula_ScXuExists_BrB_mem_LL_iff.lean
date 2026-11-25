-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.mem_LL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:10.038557+00:00
-- url     : https://prove2.me/submissions/52006a31-0e0b-4515-aebe-05e1f5db98f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorNsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_sigV_alg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_exists_of_mem_span
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (hinj : Function.Injective (piHom (sigV I v) p1))
    (hε : ∀ w ∈ LL I v, ε • w ∈ LL I v) (x : Fin I.n → RV I v) :
    x ∈ LL I v ↔ vec1 p1 x ∈ Lam1 I v p1 ∧ vec2 p1 x ∈ Lam2 I v p1 := by
  obtain ⟨hp1, hpe, hpse, -⟩ := hp
  constructor
  · intro hx
    exact ⟨Submodule.subset_span (Set.mem_image_of_mem _ hx), Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x1, hx1, e1⟩ := exists_of_mem_span I v p1 hp1 (vec1 p1 x) h1
    have hq2 : ∀ c, (p1.comp (sigV I v)) (algebraMap (KV I v) (RV I v) c) = c := by
      intro c
      rw [RingHom.comp_apply, sigV_alg, hp1]
    obtain ⟨x2, hx2, e2⟩ := exists_of_mem_span I v (p1.comp (sigV I v)) hq2 (vec2 p1 x) h2
    have hw : ε • x1 + (x2 - ε • x2) ∈ LL I v :=
      (LL I v).add_mem (hε x1 hx1) ((LL I v).sub_mem hx2 (hε x2 hx2))
    have hxw : x = ε • x1 + (x2 - ε • x2) := by
      funext i
      apply hinj
      have f1 : p1 (x1 i) = p1 (x i) := congrFun e1 i
      have f2 : p1 (sigV I v (x2 i)) = p1 (sigV I v (x i)) := congrFun e2 i
      simp only [piHom, RingHom.prod_apply, RingHom.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, map_add, map_sub, map_mul, hpe, hpse, f1, f2]
      refine Prod.ext ?_ ?_ <;> simp
    rw [hxw]
    exact hw
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
