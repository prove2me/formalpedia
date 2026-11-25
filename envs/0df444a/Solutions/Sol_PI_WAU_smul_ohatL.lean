-- Prove2me | solution 1 for PI.WAU.smul_ohatL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:22.435731+00:00
-- url     : https://prove2.me/submissions/2d41e6ab-638c-4362-89fc-7b1b50a1c3d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_ohat_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
namespace PI.WAU
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  let T : Subring (E ⊗[F] Af) :=
    { carrier := {a | ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L}
      mul_mem' := fun {a c} ha hc y hy => by rw [mul_smul]; exact ha _ (hc y hy)
      one_mem' := fun y hy => by rw [one_smul]; exact hy
      add_mem' := fun {a c} ha hc y hy => by rw [add_smul]; exact add_mem (ha y hy) (hc y hy)
      zero_mem' := fun y _ => by rw [zero_smul]; exact zero_mem _
      neg_mem' := fun {a} ha y hy => by rw [neg_smul]; exact neg_mem (ha y hy) }
  have hle : IntAf F E ≤ T := by
    apply Subring.closure_le.mpr
    rintro a (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, o • l, L.smul_mem o hl, ?_⟩
        funext i
        show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af)) * (((1 : E) ⊗ₜ[F] c) * ((l i) ⊗ₜ[F] (1 : Af))) =
          ((1 : E) ⊗ₜ[F] c) * (((o • l) i) ⊗ₜ[F] (1 : Af))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul, mul_one]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
    · refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  exact hle ha
end PI.WAU
