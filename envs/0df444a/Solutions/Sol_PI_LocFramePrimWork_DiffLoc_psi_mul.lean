-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_psi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:01.738462+00:00
-- url     : https://prove2.me/submissions/7b1827e6-ad76-4427-96ba-320118f4afc1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul_mem
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_span_le
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_frac_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (I J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    DiffLoc_psi v ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      DiffLoc_psi v (I : Set E) * DiffLoc_psi v (J : Set E) := by
  apply le_antisymm
  · have h : ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
        (Submodule.span (𝓞 E) ((I : Set E) * (J : Set E)) : Set E) := by
      show (((I * J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) : Set E) = _
      rw [FractionalIdeal.coe_mul, Submodule.mul_eq_span_mul_set]
      rfl
    rw [h]
    apply DiffLoc_span_le
    · intro o y hy
      refine Submodule.mul_induction_on (C := fun y =>
        inclR (F := F) (Fv F v) (o : E) * y ∈ DiffLoc_psi v (I : Set E) * DiffLoc_psi v (J : Set E))
        hy (fun m hm n hn => ?_) (fun x y hx hy => ?_)
      · rw [← mul_assoc]
        exact Submodule.mul_mem_mul (DiffLoc_psi_mul_mem v _ (DiffLoc_frac_closed I) hm o) hn
      · rw [mul_add]; exact add_mem hx hy
    · rintro _ ⟨i, hi, j, hj, rfl⟩
      rw [map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, hi, rfl⟩) (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [DiffLoc_psi, DiffLoc_psi, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    show inclR (F := F) (Fv F v) i * inclR (F := F) (Fv F v) j ∈ _
    rw [← map_mul]
    exact Submodule.subset_span ⟨i * j, FractionalIdeal.mul_mem_mul hi hj, rfl⟩
end PI.LocFramePrimWork
