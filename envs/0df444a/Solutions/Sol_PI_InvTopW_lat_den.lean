-- Prove2me | solution 1 for PI.InvTopW.lat_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:54:55.0421+00:00
-- url     : https://prove2.me/submissions/a92e7387-ea27-4f07-93be-c6dde576ab42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_inclE_mem_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.InvTopW
theorem _root_.solution {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ x ∈ L, ∀ i, (c : E) * x i ∈ Formalism.UG.intOE E) :
    ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) L, ∀ i,
      (c : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ Formalism.MainNotions.S.IntAf F E := by
  intro y hy
  let K : Submodule (Formalism.MainNotions.S.IntAf F E) (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :=
    { carrier := {y | ∀ i, (c : E ⊗[F] Formalism.MainNotions.S.Af F) * y i ∈ Formalism.MainNotions.S.IntAf F E}
      add_mem' := by
        intro a b ha hb i
        rw [Pi.add_apply, mul_add]
        exact add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [Pi.zero_apply, mul_zero]
        exact zero_mem _
      smul_mem' := by
        intro r a ha i
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
        exact mul_mem r.2 (ha i) }
  have hK : Formalism.MainNotions.S.lamAf (F := F) L ≤ K := by
    unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    show ∀ i, (c : E ⊗[F] Formalism.MainNotions.S.Af F) * Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) ((x : Fin n → E) i) ∈
      Formalism.MainNotions.S.IntAf F E
    intro i
    have h := inclE_mem_int (F := F) _ (hc x x.2 i)
    rw [map_mul, map_natCast] at h
    exact h
  exact hK hy
end PI.InvTopW
