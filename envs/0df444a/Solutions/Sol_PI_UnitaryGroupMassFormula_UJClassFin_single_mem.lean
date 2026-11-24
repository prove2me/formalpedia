-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:29.97607+00:00
-- url     : https://prove2.me/submissions/a31805cc-fe24-42bf-940d-f2d1a874261c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_tmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {p : Af F ⊗[F] E} (hp : p ∈ Oh F E) (l : Fin M) : Pi.single l (k • p) ∈ latHat F E L := by
  let S' : AddSubgroup (Af F ⊗[F] E) :=
    { carrier := {q | Pi.single l (k • q) ∈ latHat F E L}
      add_mem' := fun {a b} ha hb => by
        show Pi.single l (k • (a + b)) ∈ latHat F E L
        rw [smul_add, Pi.single_add]
        exact add_mem ha hb
      zero_mem' := by
        show Pi.single l (k • (0 : Af F ⊗[F] E)) ∈ latHat F E L
        rw [smul_zero, Pi.single_zero]
        exact zero_mem _
      neg_mem' := fun {a} ha => by
        show Pi.single l (k • (-a)) ∈ latHat F E L
        rw [smul_neg, Pi.single_neg]
        exact neg_mem ha }
  have hsub : {r : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e} ⊆
      (S' : Set _) := by
    rintro r ⟨a, ha, e, he, rfl⟩
    show Pi.single l (k • (a ⊗ₜ[F] e)) ∈ latHat F E L
    rw [nsmul_tmul_F, single_tmul]
    unfold latHat
    exact AddSubgroup.subset_closure ⟨a, ha, Pi.single l ((k : F) • e), hk l e he, rfl⟩
  exact (AddSubgroup.closure_le S').mpr hsub hp
end PI.UnitaryGroupMassFormula.UJClassFin
