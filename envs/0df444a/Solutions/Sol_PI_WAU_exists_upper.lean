-- Prove2me | solution 1 for PI.WAU.exists_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:55.656562+00:00
-- url     : https://prove2.me/submissions/1467bd9e-ba88-48bd-b3af-e10147ee5af9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Theorems.Thm_PI_WAU_lamAf_le_ohatL
import Theorems.Thm_PI_WAU_intC_zero
import Theorems.Thm_PI_WAU_intC_neg
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_exists_den_fin
import Theorems.Thm_PI_WAU_intC_add
import Theorems.Thm_PI_WAU_ohat_add
import Theorems.Thm_PI_WAU_ohat_mul
import Theorems.Thm_PI_WAU_ohat_zero
import Theorems.Thm_PI_WAU_ohat_zsmul
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.WAU
theorem _root_.solution (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨T, hT⟩ := (hfg.restrictScalars (R := ℤ))
  obtain ⟨D, hD, hDint⟩ := exists_den_fin (fun x : T × Fin n × ι =>
    b.repr ((x.1 : Fin n → E) x.2.1) x.2.2)
  have hQ : ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
    intro l hl
    have hl' : l ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by rw [hT]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem x hx => intro j k; exact hDint ⟨⟨x, hx⟩, j, k⟩
    | zero =>
      intro j k
      unfold IntF
      simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero, mul_zero]
      exact ohat_zero
    | add x z _ _ hx hz =>
      intro j k
      have h1 := hx j k
      have h2 := hz j k
      unfold IntF at h1 h2 ⊢
      rw [Pi.add_apply, map_add, Finsupp.add_apply, mul_add, map_add]
      exact ohat_add h1 h2
    | smul a x _ hx =>
      intro j k
      have h1 := hx j k
      unfold IntF at h1 ⊢
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, mul_smul_comm, map_zsmul]
      exact ohat_zsmul h1 a
  refine ⟨D, hD, fun y hy j => ?_⟩
  have hy' := lamAf_le_ohatL L hy
  clear hy
  unfold ohatL at hy'
  induction hy' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    intro k
    rw [map_nsmul, Pi.smul_apply]
    have ew : ((((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)) j) =
        (l j) ⊗ₜ[F] c := by
      simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [ew]
    simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, Algebra.smul_def]
    exact ohat_mul (hQ l hl j k) hc
  | zero => rw [Pi.zero_apply, smul_zero]; exact intC_zero
  | add u w _ _ hu hw => rw [Pi.add_apply, smul_add]; exact intC_add hu hw
  | neg u _ hu => rw [Pi.neg_apply, smul_neg]; exact intC_neg hu
end PI.WAU
