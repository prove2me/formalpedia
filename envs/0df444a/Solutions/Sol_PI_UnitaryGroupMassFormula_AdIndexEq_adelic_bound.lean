-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.adelic_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:51.971143+00:00
-- url     : https://prove2.me/submissions/9aa6f48e-eeee-403d-b4fb-1cbc775f7398

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_WAU_B_common_nat
import Theorems.Thm_PI_WAU_B_exists_gen
import Theorems.Thm_PI_WAU_B_exists_nat_vec
import Theorems.Thm_PI_WAU_B_mulVec_lam
import Theorems.Thm_PI_WAU_B_nsmul_lam


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
theorem _root_.solution (I : AutInst) (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf := by
  obtain ⟨k, m, hm, hgen⟩ := PI.WAU.B.exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  obtain ⟨N, hN0, hN⟩ := PI.WAU.B.common_nat
    (fun j N => N • (Mx *ᵥ PI.WAU.B.ivec (F := I.F) (m j)) ∈ I.Lf)
    (fun j N M h => PI.WAU.B.nsmul_lam h M)
    (fun j => PI.WAU.B.exists_nat_vec (F := I.F) I.L_span _)
  refine ⟨N, hN0, fun w hw => ?_⟩
  have := PI.WAU.B.mulVec_lam hm hgen (N • Mx) (fun j => by rw [Matrix.smul_mulVec]; exact hN j) hw
  rwa [Matrix.smul_mulVec] at this
end PI.UnitaryGroupMassFormula.AdIndexEq
