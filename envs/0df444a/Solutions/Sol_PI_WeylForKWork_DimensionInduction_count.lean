-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:15.347256+00:00
-- url     : https://prove2.me/submissions/73ff8377-cae7-41d5-90e8-afaeffd07d90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_comm_comp
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_exists_hit
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_into
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_kill
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_proj_comm
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_schur2
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_inf
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_map
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_orth
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
open PI PI.WeylForKWork PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*} {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
namespace PI.WeylForKWork.DimensionInduction
theorem _root_.solution (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X : Submodule ℂ H} [FiniteDimensional ℂ S] (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0) :
    ∀ n, ∀ W : Submodule ℂ H, W ≤ S → Stab ρ W → finrank ℂ W = n →
      finrank ℂ W = finrank ℂ X * finrank ℂ ↥(slice ρ x₀ ⊓ W) := by
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro W hWS hWs hWn
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  by_cases hW0 : W = ⊥
  · subst hW0
    simp
  obtain ⟨c, hc, hcW, hc0⟩ := exists_hit hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 hWS hW0 hWs
  have hcX : ∀ x ∈ X, c x ∈ W := into hρ hc hWs hXs hXi hx₀ h0 hcW
  have hYW : X.map c ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcX x hx
  have hYs : Stab ρ (X.map c) := stab_map hc hXs
  haveI : FiniteDimensional ℂ (X.map c) := Submodule.finiteDimensional_of_le hYW
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hYrank : finrank ℂ (X.map c) = finrank ℂ X := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  have hYi : Irr ρ (X.map c) := by
    intro Y' hY'Y hY's
    have hst : Stab ρ (X ⊓ Y'.comap c) := stab_inf hXs (fun i v hv => by
      show c (ρ i v) ∈ Y'
      rw [hc i v]
      exact hY's i _ hv)
    rcases hXi _ inf_le_left hst with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hY'Y hy
      have hm : x ∈ X ⊓ Y'.comap c := ⟨hx, hy⟩
      rw [h] at hm
      rw [(Submodule.mem_bot ℂ).1 hm, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hY'Y
      rintro _ ⟨x, hx, rfl⟩
      have hm : x ∈ X ⊓ Y'.comap c := by
        rw [h]
        exact hx
      exact hm.2
  have hYpos : 0 < finrank ℂ (X.map c) :=
    finrank_pos_iff_exists_ne_zero.2 ⟨⟨c x₀, x₀, hx₀, rfl⟩, fun h => hc0 (congrArg Subtype.val h)⟩
  have hW's : Stab ρ ((X.map c)ᗮ ⊓ W) := stab_inf (stab_orth hρ hYs) hWs
  have hW'S : (X.map c)ᗮ ⊓ W ≤ S := inf_le_right.trans hWS
  have hsum := Submodule.finrank_add_inf_finrank_orthogonal hYW
  have hsl : slice ρ x₀ ⊓ W = (ℂ ∙ c x₀) ⊔ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) := by
    apply le_antisymm
    · rintro z ⟨⟨d, hd, rfl⟩, hzW⟩
      set P : H →ₗ[ℂ] H := ((X.map c).starProjection : H →ₗ[ℂ] H) with hP
      have hPd : Comm ρ (P ∘ₗ d) := comm_comp (proj_comm hρ hYs) hd
      have hPdY : (P ∘ₗ d) x₀ ∈ X.map c := by
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact ((X.map c).orthogonalProjection _).2
      obtain ⟨μ, hμ⟩ := (schur2 hρ hXs hXi hYs hYi hx₀ h0 hc hPd ⟨x₀, hx₀, rfl⟩ hc0 hPdY).2
      refine Submodule.mem_sup.2 ⟨μ • c x₀, Submodule.smul_mem _ μ (Submodule.mem_span_singleton_self _),
        d x₀ - μ • c x₀, ⟨?_, ?_, ?_⟩, by abel⟩
      · exact ⟨d - μ • c, (commSub ρ).sub_mem hd ((commSub ρ).smul_mem μ hc), rfl⟩
      · rw [← hμ]
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact (X.map c).sub_starProjection_mem_orthogonal _
      · exact W.sub_mem hzW (W.smul_mem μ hcW)
    · refine sup_le ?_ (inf_le_inf_left _ inf_le_right)
      exact (Submodule.span_singleton_le_iff_mem _ _).2 ⟨⟨c, hc, rfl⟩, hcW⟩
  have hdisj : (ℂ ∙ c x₀) ⊓ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, -, hz2, -⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    have hin := (Submodule.mem_orthogonal _ _).1 hz2 (c x₀) ⟨x₀, hx₀, rfl⟩
    rw [inner_smul_right] at hin
    rcases mul_eq_zero.1 hin with ha | ha
    · rw [ha, zero_smul]
      exact Submodule.zero_mem _
    · exact absurd (inner_self_eq_zero.1 ha) hc0
  have hrk1 : finrank ℂ (ℂ ∙ c x₀) = 1 := finrank_span_singleton hc0
  haveI : FiniteDimensional ℂ ↥(slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) :=
    Submodule.finiteDimensional_of_le (inf_le_right.trans inf_le_right)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ c x₀) (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W))
  rw [hdisj, finrank_bot, add_zero, ← hsl, hrk1] at hsup
  have hih := ih (finrank ℂ ↥((X.map c)ᗮ ⊓ W)) (by omega) _ hW'S hW's rfl
  rw [hsup, ← hsum, hYrank, hih]
  ring
end PI.WeylForKWork.DimensionInduction
