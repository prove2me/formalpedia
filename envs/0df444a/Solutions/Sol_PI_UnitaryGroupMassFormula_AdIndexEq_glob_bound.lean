-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.glob_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:22.118877+00:00
-- url     : https://prove2.me/submissions/fd429a38-0de9-434f-a87d-c77ee0aa9133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Theorems.Thm_PI_WAU_B_exists_PN
import Theorems.Thm_PI_WAU_B_exists_gen
import Theorems.Thm_PI_WAU_B_mulVec_lam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (x : I.Gf) :
    ∃ N : ℕ, 0 < N ∧ (∀ w ∈ I.Lf, N • (I.fmat x *ᵥ w) ∈ I.Lf) ∧
      (∀ w ∈ I.Lf, N • (I.fmat x⁻¹ *ᵥ w) ∈ I.Lf) := by
  obtain ⟨k, m, hm, hgen⟩ := PI.WAU.B.exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  obtain ⟨N, hN⟩ := PI.WAU.B.exists_PN I m x
  refine ⟨N, hN.1, fun w hw => ?_, fun w hw => ?_⟩
  · have := PI.WAU.B.mulVec_lam hm hgen (N • I.fmat x)
      (fun j => by rw [Matrix.smul_mulVec]; exact (hN.2 j).1) hw
    rwa [Matrix.smul_mulVec] at this
  · have := PI.WAU.B.mulVec_lam hm hgen (N • I.fmat x⁻¹)
      (fun j => by rw [Matrix.smul_mulVec]; exact (hN.2 j).2) hw
    rwa [Matrix.smul_mulVec] at this
end PI.UnitaryGroupMassFormula.AdIndexEq
