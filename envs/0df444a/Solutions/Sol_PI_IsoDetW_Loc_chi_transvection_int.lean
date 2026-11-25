-- Prove2me | solution 1 for PI.IsoDetW.Loc.chi_transvection_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:37.156801+00:00
-- url     : https://prove2.me/submissions/5bda12bb-0222-4895-a51a-3918bb86b7b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
import Theorems.Thm_PI_IsoDetW_Loc_map_std_eq
import Theorems.Thm_PI_IsoDetW_Loc_lidx_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (z : R) :
    chi R P (Matrix.transvection i j (algebraMap R K z)) = 0 := by
  have hint : ∀ c : R, ∀ a b, ∃ w : R, algebraMap R K w = Matrix.transvection i j (algebraMap R K c) a b := by
    intro c a b
    refine ⟨Matrix.transvection i j c a b, ?_⟩
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [chi, map_std_eq (hint z) (g' := Matrix.transvection i j (algebraMap R K (-z))) (hint (-z))
    (by rw [Matrix.transvection_mul_transvection_same i j hij, ← map_add, add_neg_cancel, map_zero,
      Matrix.transvection_zero]), lidx_self]
end PI.IsoDetW.Loc
