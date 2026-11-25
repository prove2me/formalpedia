-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:51.237885+00:00
-- url     : https://prove2.me/submissions/838e09ab-37e8-4846-83fe-055f460fcc8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_int_eq_mul_1252f130419c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
variable {L : Type} [Field L]
variable [NumberField L] {B : Subring L} [Module.Finite ℤ B]
namespace GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
theorem _root_.solution : ∃ S : Set (𝓞 L), S.Finite ∧ LinearIndepOn B (fun x : 𝓞 L => (x : L)) S ∧
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : 𝓞 L,
      (N : L) * (x : L) ∈ Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_maximal_linearIndepOn B (fun x : 𝓞 L => (x : L))
  set F := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hF
  have hfin : S.Finite := by
    have h1 : LinearIndependent ℤ (fun x : S => ((x : 𝓞 L) : L)) := hS.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ (fun x : S => (x : 𝓞 L)) :=
      LinearIndependent.of_comp (algebraMap (𝓞 L) L).toIntAlgHom.toLinearMap h1
    exact Set.finite_coe_iff.mp h2.finite
  refine ⟨S, hfin, hS, ?_⟩
  have hone : ∀ x : 𝓞 L, ∃ c : ℤ, c ≠ 0 ∧ (c : L) * (x : L) ∈ F := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
    · obtain ⟨a, ha, hax⟩ := hmax x hx
      obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ha
      refine ⟨c, hc, ?_⟩
      have h1 : (c : L) * (x : L) = q • (a • (x : L)) := by
        have h2 : (c : L) = ((c : B) : L) := by push_cast; rfl
        rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, h2, hcq]
        push_cast
        ring
      rw [h1]
      exact F.smul_mem q hax
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 L)
  choose c hc0 hcF using hone
  set N := ∏ g ∈ T, c g with hN
  refine ⟨N, Finset.prod_ne_zero_iff.mpr fun g _ => hc0 g, ?_⟩
  have hgen : ∀ g ∈ T, (N : L) * (g : L) ∈ F := by
    intro g hg
    have h1 : (N : L) * (g : L) = (∏ h ∈ T.erase g, c h) • ((c g : L) * (g : L)) := by
      rw [hN, ← Finset.mul_prod_erase T c hg, zsmul_eq_mul]
      push_cast
      ring
    rw [h1]
    exact F.toAddSubgroup.zsmul_mem (hcF g) _
  intro x
  have hx : x ∈ Submodule.span ℤ (T : Set (𝓞 L)) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz =>
    have h1 : (N : L) * ((y + z : 𝓞 L) : L) = (N : L) * (y : L) + (N : L) * (z : L) := by
      push_cast
      ring
    rw [h1]
    exact F.add_mem hy hz
  | smul n y _ hy =>
    have h1 : (N : L) * ((n • y : 𝓞 L) : L) = n • ((N : L) * (y : L)) := by
      have h2 : ((n • y : 𝓞 L) : L) = n • (y : L) := map_zsmul (algebraMap (𝓞 L) L) n y
      rw [h2, mul_smul_comm]
    rw [h1]
    exact F.toAddSubgroup.zsmul_mem hy _
end GroundTheory.Heights₂.Heights.OrderIdealIndexExtensionAlt
