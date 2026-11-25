-- Prove2me | solution 1 for PI.Dv.TIW.idx_le_natSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:58.609227+00:00
-- url     : https://prove2.me/submissions/62ef1af4-36bf-44ad-b7fe-bc23c9bb58cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_PI_Dv_TIW_mem_smulSub
import Theorems.Thm_PI_Dv_TIW_span_smulSub
import Theorems.Thm_PI_Dv_TIW_fg_smulSub
import Theorems.Thm_PI_Dv_TIW_idx_le_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 0 < m)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub ((m : ℕ) : K) M) ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((m : ℕ) : K) := by
  have hmK : ((m : ℕ) : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine idx_le_nat hI w M _ hM (fg_smulSub _ M hM) (span_smulSub _ hmK M).symm m hm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
    rw [Nat.cast_smul_eq_nsmul K m y, ← Nat.cast_smul_eq_nsmul (𝓞 K) m y]
    exact Submodule.smul_mem _ _ hy
  · intro x hx
    refine (mem_smulSub _ M _).mpr ⟨x, hx, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end PI.Dv.TIW
