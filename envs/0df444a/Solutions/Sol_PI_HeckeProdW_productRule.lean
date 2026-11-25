-- Prove2me | solution 1 for PI.HeckeProdW.productRule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:06.087279+00:00
-- url     : https://prove2.me/submissions/794dd8db-2b46-4317-9b5d-a1e70505067d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_PI_HeckeProdW_f_inv_mul
import Theorems.Thm_P2M_PI_HeckeProdW_f_inv_mul__f59e1f1fa06b
import Theorems.Thm_PI_HeckeProdW_chi_unit
import Theorems.Thm_PI_HeckeProdW_pw_local
import Theorems.Thm_PI_HeckeProdW_pv_local_self
import Theorems.Thm_PI_HeckeProdW_pv_local_ne
import Theorems.Thm_PI_HeckeProdW_pw_infDiag
import Theorems.Thm_PI_HeckeProdW_pv_infDiag
import Theorems.Thm_PI_HeckeProdW_pw_diag
import Theorems.Thm_PI_HeckeProdW_pv_diag
import Theorems.Thm_PI_HeckeProdW_locK_eq
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_diag_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution (χ : HChar L) : χ.ProductRule := by
  classical
  intro S hS k
  have hfin : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = 1}.Finite :=
    Filter.eventually_cofinite.1 (valued_comp_eventually L (diagUnits L k))
  set T0 : Finset (HeightOneSpectrum (𝓞 L)) := S ∪ hfin.toFinset with hT0
  set A : Ideles L := infDiag k * ∏ v ∈ T0, localIdele L v (atFin v k) with hA
  set u : Ideles L := A⁻¹ * diagUnits L k with hu
  have hAw : ∀ w, pw w A = pw w (diagUnits L k) := by
    intro w
    rw [hA, map_mul, map_prod, Finset.prod_eq_one (fun v _ => pw_local w v _), mul_one, pw_infDiag, pw_diag]
  have hAv_in : ∀ v ∈ T0, pv v A = pv v (diagUnits L k) := by
    intro v hv
    rw [hA, map_mul, map_prod, pv_infDiag, one_mul,
      Finset.prod_eq_single v (fun b _ hb => pv_local_ne b v (Ne.symm hb) _) (fun h => absurd hv h),
      pv_local_self, pv_diag]
  have hAv_out : ∀ v ∉ T0, pv v A = 1 := by
    intro v hv
    rw [hA, map_mul, map_prod, pv_infDiag, one_mul]
    exact Finset.prod_eq_one fun b hb => pv_local_ne b v (fun h => hv (h ▸ hb)) _
  have hu1 : χ.1 u = 1 := by
    apply chi_unit χ u
    · funext w
      exact f_inv_mul (pw w) A _ (hAw w)
    · intro v
      by_cases hv : v ∈ T0
      · show Valued.v (pv v u) = 1
        rw [hu, f_inv_mul (pv v) A _ (hAv_in v hv)]
        exact map_one _
      · show Valued.v (pv v u) = 1
        rw [hu, f_inv_mul' (pv v) A _ (hAv_out v hv)]
        by_contra h
        exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
    · intro v hne
      have hv : v ∉ T0 := fun hv => hne (by
        show pv v u = 1
        rw [hu, f_inv_mul (pv v) A _ (hAv_in v hv)])
      exact hS v (fun h => hv (Finset.mem_union_left _ h))
  have hD : diagUnits L k = A * u := by rw [hu, mul_inv_cancel_left]
  have hmain : χ.inf k * ∏ v ∈ T0, χ.locK v k = 1 := by
    have h := χ.2.2 k
    rw [hD, map_mul, hu1, mul_one, hA, map_mul, map_prod] at h
    exact h
  have hord : ∀ v ∉ T0, ordF v k = 0 := by
    intro v hv
    have h1 : Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = 1 := by
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
    rw [diag_comp] at h1
    simp [ordF, h1]
  have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = ∏ v ∈ T0 \ S, χ.locK v k := by
    change (∏ᶠ v ∈ ((S : Set (HeightOneSpectrum (𝓞 L)))ᶜ), χ.val v ^ ordF v k) = _
    rw [finprod_mem_eq_prod_of_subset _ (t := T0 \ S)]
    · exact Finset.prod_congr rfl fun v hv => (locK_eq χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
    · rintro v ⟨hvS, hvf⟩
      rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      refine ⟨?_, hvS⟩
      by_contra hv
      exact hvf (by show χ.val v ^ ordF v k = 1; rw [hord v hv, zpow_zero])
    · intro v hv
      rw [Finset.coe_sdiff] at hv
      exact hv.2
  rw [hfp, mul_assoc, mul_comm (∏ v ∈ S, χ.locK v k), Finset.prod_sdiff Finset.subset_union_left]
  exact hmain
end PI.HeckeProdW
