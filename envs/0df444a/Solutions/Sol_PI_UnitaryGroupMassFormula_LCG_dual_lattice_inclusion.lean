-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.dual_lattice_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:18.177791+00:00
-- url     : https://prove2.me/submissions/ea26a880-221f-415a-8f58-7b814905b324

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_sig_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_mem_latSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_hform_sub_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DualI_pair_int
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_adelstabL_den
import Theorems.Thm_Formalism_UG_P_adelstabL_incl_int
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_csDual_expand
import Theorems.Thm_Formalism_UG_P_csDual_hform_incl
import Theorems.Thm_Formalism_UG_P_csDual_hform_smul_left
import Theorems.Thm_Formalism_UG_P_csDual_sig_C
import Theorems.Thm_Formalism_UG_P_csDual_span
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_int
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_sf_single
import Theorems.Thm_Formalism_UG_P_span_recovery_of_integral_adelic_approx
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
open NumberField Matrix TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open DualI Formalism.UG Formalism.UG.P
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : DualIncl := by
  intro I y u hu
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hdet : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set g : GL (Fin I.n) (AA I) := (y.2 : GL (Fin I.n) (AA I)) with hg
  have hU : cT (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (g : Matrix (Fin I.n) (Fin I.n) (AA I)) * I.J.map (iA I) *
      (g : Matrix (Fin I.n) (Fin I.n) (AA I)) = I.J.map (iA I) := y.2.2

  have hu' : ∀ w ∈ Formalism.UG.CS.globLat g I.L, hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J w u ∈
      (algebraMap (𝓞 I.E) I.E).range := by
    intro w hw
    apply hu w
    rw [mem_latSet]
    exact hw
  obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ
      (fun i => iA I (u i)) := ⟨_, rfl⟩
  have hxz : (fun i => iA I (u i)) = (g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ z := by
    rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]

  have hw : ∀ w ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L,
      hform (sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.J.map (iA I)) w z ∈ SS I := by
    intro w hw
    have hu2 := (span_recovery_of_integral_adelic_approx csGlob_intAdApprox I.F I.E (Fin I.n) I.L hfin I.L_span g
      ((g : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ w)).2
      (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
    have := csDual_span I.cm.sig I.J (Formalism.UG.CS.globLat g I.L) u hu' _ hu2
    rwa [hxz, hform_mulVec, hU] at this
  obtain ⟨c, hc, hlow⟩ := adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Fin I.n × Fin I.n => (I.J⁻¹) p.1 p.2)
  have hi : ∀ i, levelafC I.E c * ((I.J.map (iA I)) *ᵥ z) i ∈ SS I := by
    intro i
    have h1 := hw _ (hlow (Pi.single i (1 : AA I)) (fun k => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _))
    have h2 : (fun k => levelafC I.E c * (Pi.single i (1 : AA I) : Fin I.n → _) k) =
        levelafC I.E c • (Pi.single i (1 : AA I) : Fin I.n → _) := by
      funext k; simp [Pi.smul_apply]
    rwa [h2, csDual_hform_smul_left, csDual_sig_C, sf_single] at h1
  have hinv : (I.J⁻¹).map (iA I) * I.J.map (iA I) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul I.J hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz2 : (I.J⁻¹).map (iA I) *ᵥ ((I.J.map (iA I)) *ᵥ z) = z := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hv : ∀ k, levelafC I.E c * iA I (m : I.E) * z k ∈ SS I := by
    intro k
    have := csDual_expand (F := I.F) (I.J⁻¹) ((I.J.map (iA I)) *ᵥ z) (levelafC I.E c) (iA I (m : I.E)) k
    rw [hz2] at this
    rw [this]
    refine sum_mem fun i _ => mul_mem ?_ (hi i)
    rw [← map_mul]
    exact adelstabL_incl_int (F := I.F) _ (hm (k, i))

  set D : 𝓞 I.F := c * (m : 𝓞 I.F) with hD
  have hD0 : D ≠ 0 := mul_ne_zero hc (Int.cast_ne_zero.2 hm0)
  have hmC : levelafC I.E ((m : 𝓞 I.F)) = iA I (m : I.E) := by
    rw [← adelstab_incl_C, map_intCast]
  have hDl : levelafC I.E D = levelafC I.E c * iA I (m : I.E) := by
    rw [hD, levelafC_mul, hmC]
  have hDE : algebraMap (𝓞 I.F) I.E D ≠ 0 := adelstab_algebraMap_ne_zero (F := I.F) (E := I.E) D hD0
  have happ : ∀ k, ∃ b : 𝓞 I.E, ∃ t ∈ SS I, levelafC I.E D * z k =
      iA I (algebraMap (𝓞 I.E) I.E b) + levelafC I.E (D * c) * t := by
    intro k
    obtain ⟨b, t, ht, hbt⟩ := csGlob_approx (F := I.F) (E := I.E) csGlob_intAdApprox (D * c)
      (mul_ne_zero hD0 hc) (levelafC I.E D * z k) (by rw [hDl]; exact hv k)
    exact ⟨b, t, ht, hbt⟩
  choose b t ht hbt using happ
  set v : Fin I.n → I.E := fun k => algebraMap (𝓞 I.E) I.E (b k) * (algebraMap (𝓞 I.F) I.E D)⁻¹ with hvdef
  have hq : iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * levelafC I.E D = 1 := by
    rw [← adelstab_incl_C, ← map_mul, inv_mul_cancel₀ hDE, map_one]
  have hzk : ∀ k, z k = iA I (v k) + levelafC I.E c * t k := by
    intro k
    have h1 := hbt k
    rw [levelafC_mul D c] at h1
    have h3 : iA I (v k) = iA I (algebraMap (𝓞 I.E) I.E (b k)) * iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) := by
      rw [hvdef]; exact map_mul _ _ _
    rw [h3]
    linear_combination iA I ((algebraMap (𝓞 I.F) I.E D)⁻¹) * h1 - z k * hq + (levelafC I.E c * t k) * hq
  have hct : (fun k => levelafC I.E c * t k) ∈ latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (SS I) I.L := hlow _ ht
  have hzv : (fun k => iA I (v k)) = z - (fun k => levelafC I.E c * t k) := by
    funext k
    rw [Pi.sub_apply, hzk k]
    ring

  have hvL : v ∈ I.L := by
    rw [I.L_dual v]
    intro w hwL
    have hint : IsIntegral ℤ (Formalism.UG.hform (starRingEnd I.E) I.J w v) := by
      apply csGlob_int (F := I.F)
      rw [← sig_eq, ← csDual_hform_incl, hzv, hform_sub_right]
      exact sub_mem (hw _ (Submodule.subset_span ⟨w, hwL, rfl⟩)) (pair_int I w hwL _ hct)
    exact ⟨⟨_, hint⟩, rfl⟩
  rw [mem_latSet]
  show ((g⁻¹ : GL (Fin I.n) (AA I)) : Matrix (Fin I.n) (Fin I.n) (AA I)) *ᵥ (fun i => iA I (u i)) ∈ _
  rw [← hz]
  have hz3 : z = (fun k => iA I (v k)) + (fun k => levelafC I.E c * t k) := by
    rw [hzv]; abel
  rw [hz3]
  exact add_mem (Submodule.subset_span ⟨v, hvL, rfl⟩) hct
end PI.UnitaryGroupMassFormula.LCG
