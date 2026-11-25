-- Prove2me | solution 1 for P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:48.341797+00:00
-- url     : https://prove2.me/submissions/df0fd1a6-0b4e-41b4-bf69-bda70b2be67f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.DvRows
theorem _root_.solution (X Y : Submodule R V)
    (h : Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V)) :
    X ≤ locS (nonZeroDivisors R) Y := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors R) Y
      add_mem' := (locS (nonZeroDivisors R) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors R) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
        have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
          field_simp
        have : (b * d) • ((algebraMap R K a / algebraMap R K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  intro x hx
  exact hle (h (Submodule.subset_span hx))
end PI.DvRows
