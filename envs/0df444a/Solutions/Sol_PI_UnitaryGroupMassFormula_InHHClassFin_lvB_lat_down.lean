-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvB_lat_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:05.965005+00:00
-- url     : https://prove2.me/submissions/06bdf195-663c-4be4-ad69-60b9ff91d156

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvB_C_intCast
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvB_span_int
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, y i ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) →
      levelafC E d • y ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  classical
  choose m hm0 hm using fun i : Fin n =>
    lvB_span_int L (Pi.single i 1) (hspan ▸ Submodule.mem_top)
  set M : ℤ := ∏ i, m i with hMdef
  have hM : ∀ i, M • (Pi.single i (1 : E) : Fin n → E) ∈ L := fun i => by
    rw [hMdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
    exact zsmul_mem (hm i) _
  refine ⟨(M : 𝓞 F), Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hm0 i), ?_⟩
  intro y hy
  rw [lvB_C_intCast]
  have e : (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • y =
      ∑ i, (⟨y i, hy i⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
        (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
          ((M • (Pi.single i (1 : E) : Fin n → E)) j)) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Subring.smul_def,
      Pi.single_apply, zsmul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hM i⟩, rfl⟩)
end PI.UnitaryGroupMassFormula.InHHClassFin
