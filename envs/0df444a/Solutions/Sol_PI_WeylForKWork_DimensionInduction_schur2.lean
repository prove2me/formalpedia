-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.schur2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.340163+00:00
-- url     : https://prove2.me/submissions/7fbc5220-d235-4e94-99a9-d68ed6aae409

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_kill
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_into
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_map
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
variable {ι κ : Type*}
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
namespace PI.WeylForKWork.DimensionInduction
theorem _root_.solution (hρ : Good ρ) {X W : Submodule ℂ H} [FiniteDimensional ℂ X] [FiniteDimensional ℂ W]
    (hXs : Stab ρ X) (hXi : Irr ρ X) (hWs : Stab ρ W) (hWi : Irr ρ W) {x₀ : H} (hx₀ : x₀ ∈ X)
    (h0 : x₀ ≠ 0) {c c' : H →ₗ[ℂ] H} (hc : Comm ρ c) (hc' : Comm ρ c') (hcW : c x₀ ∈ W)
    (hc0 : c x₀ ≠ 0) (hc'W : c' x₀ ∈ W) :
    finrank ℂ X = finrank ℂ W ∧ ∃ μ : ℂ, c' x₀ = μ • c x₀ := by
  have hAW : ∀ x : X, c x ∈ W := fun x => into hρ hc hWs hXs hXi hx₀ h0 hcW x x.2
  have hBW : ∀ x : X, c' x ∈ W := fun x => into hρ hc' hWs hXs hXi hx₀ h0 hc'W x x.2
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hmapW : X.map c = W := by
    rcases hWi _ (by rintro _ ⟨x, hx, rfl⟩; exact hAW ⟨x, hx⟩) (stab_map hc hXs) with h | h
    · exfalso
      have hm : c x₀ ∈ X.map c := ⟨x₀, hx₀, rfl⟩
      rw [h] at hm
      exact hc0 ((Submodule.mem_bot ℂ).1 hm)
    · exact h
  have hrank : finrank ℂ X = finrank ℂ W := by
    rw [← hmapW, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  refine ⟨hrank, ?_⟩
  let A : X →ₗ[ℂ] W := (c.domRestrict X).codRestrict W hAW
  let B : X →ₗ[ℂ] W := (c'.domRestrict X).codRestrict W hBW
  have hAinj : Function.Injective A := fun a b hab => hinj (congrArg Subtype.val hab)
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hAinj
  let e : X ≃ₗ[ℂ] W := LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩
  let T : Module.End ℂ X := e.symm.toLinearMap ∘ₗ B
  haveI : Nontrivial X := ⟨⟨⟨x₀, hx₀⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hBv : B v = μ • A v :=
    calc B v = e (T v) := (e.apply_symm_apply (B v)).symm
      _ = e (μ • v) := by rw [hTv]
      _ = μ • e v := map_smul e μ v
      _ = μ • A v := rfl
  have hcv : c' v = μ • c v := congrArg Subtype.val hBv
  have hd : Comm ρ (c' - μ • c) := (commSub ρ).sub_mem hc' ((commSub ρ).smul_mem μ hc)
  have hdv : (c' - μ • c) v = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hcv, sub_self]
  have hv0 : (v : H) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hfin := kill hd hXs hXi v.2 hv0 hdv x₀ hx₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hfin
  exact ⟨μ, hfin⟩
end PI.WeylForKWork.DimensionInduction
