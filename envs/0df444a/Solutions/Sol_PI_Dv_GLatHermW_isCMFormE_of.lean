-- Prove2me | solution 1 for PI.Dv.GLatHermW.isCMFormE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:44.174485+00:00
-- url     : https://prove2.me/submissions/5e257e7c-bc66-40a9-88b1-b049163417f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Theorems.Thm_PI_Dv_GLatHermW_isCM_cf
import Theorems.Thm_PI_Dv_GLatHermW_isCM_mul
import Theorems.Thm_PI_Dv_GLatHermW_isCM_sum
import Theorems.Thm_PI_Dv_GLatHermW_asAlgebraHom_eG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hC : IsCMForm A ρ h) :
    IsCMFormE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨c1, c2, c3⟩ := hC
  refine ⟨c1, fun i j => ?_, c3⟩
  have he : A.b.repr ((ρ.asAlgebraHom (eG T)) (A.b j)) i =
      ∑ g : G, cf T g * A.b.repr (ρ g (A.b j)) i := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact isCM_sum _ _ fun g _ => isCM_mul (isCM_cf hS T g) (c2 g i j)
end PI.Dv.GLatHermW
