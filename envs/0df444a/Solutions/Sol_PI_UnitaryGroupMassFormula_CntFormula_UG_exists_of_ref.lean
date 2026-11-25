-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_of_ref
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:29.336815+00:00
-- url     : https://prove2.me/submissions/8b835c19-631c-463f-80ea-91da898d7f1c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_star_h
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_pair
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_isSymm_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_of_pair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {ι : Type}
    [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} {u : K} (hu : IsUnitIn S u) (hus : star u = u) (hrr : h r r = u)
    (hrx : ∀ i, h (x i) r = 0) :
    ∃ z ∈ M, h z z = u ∧ ∀ i, h (x i) z = 0 := by
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨α, hα0, hαM, w, hwM, hw1, hwx⟩ :=
    exists_pair hS hM x hxo hxu hxM ⟨r, by rw [hrr]; exact hu0⟩ hrx
  have hyy : h (α⁻¹ • r) (α⁻¹ • r) = star α⁻¹ * α⁻¹ * u := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, hrr, RingHom.id_apply]
    ring
  have hsa : star α⁻¹ * α⁻¹ ∈ S := by
    have h1 := S.mul_mem (hM.int _ hαM _ hαM) hu.2.2
    rw [hyy, mul_assoc, mul_inv_cancel₀ hu0, mul_one] at h1
    exact h1
  obtain ⟨b, hb, hab⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hsa
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hs' := isSymm_smul hs hus
  have hyw0 : h (α⁻¹ • r) w = 1 := by rw [← star_h hs, hw1, star_one]
  have hy' : (u⁻¹ • h) (α⁻¹ • r) (α⁻¹ • r) = star (α⁻¹ * b) * (α⁻¹ * b) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hyy, star_mul']
    rw [mul_comm u⁻¹, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
    linear_combination (-(star α⁻¹ * α⁻¹)) * hb
  have hyw' : (u⁻¹ • h) (α⁻¹ • r) (u • w) = 1 := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hyw0, mul_one,
      inv_mul_cancel₀ hu0]
  have hww : (u⁻¹ • h) (u • w) (u • w) = u * h w w := by
    simp only [LinearMap.smul_apply, map_smulₛₗ, map_smul, smul_eq_mul, starRingEnd_apply, hus, RingHom.id_apply]
    field_simp
  obtain ⟨c, hc, d, hd, hcd⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_of_pair hS hs'
    (y := α⁻¹ • r) (w := u • w) (a := α⁻¹ * b) hab (mul_ne_zero (inv_ne_zero hα0) hb0) hy' hyw'
    (hww ▸ S.mul_mem hu.2.1 (hM.int w hwM w hwM))
  refine ⟨c • (u • w) + d • (α⁻¹ • r),
    M.add_mem (hM.smul_mem c hc _ (hM.smul_mem u hu.2.1 w hwM)) (hM.smul_mem d hd _ hαM), ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at hcd
    exact ((inv_mul_eq_one₀ (inv_ne_zero hu0 |> fun _ => hu0)).1 hcd).symm
  · intro i
    simp [map_add, map_smul, hwx i, hrx i]
end PI.UnitaryGroupMassFormula.CntFormula.UG
