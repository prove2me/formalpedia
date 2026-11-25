-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_AdIndexEq_trace_integral__5d3ee3114f2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:26.987261+00:00
-- url     : https://prove2.me/submissions/9cf42551-8acb-410e-a49a-3103e757ab92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowD
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_incL
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_fixed_incL
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : TraceInt := by
  intro I v hv α hα
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := ⟨hv.exists_pair_ne⟩
  have hinv : ∀ y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v (sigV I v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have h1 : ∀ e' : I.E, I.cm.sig e' = star e' := fun _ => rfl
      simp [sigV, h1]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  obtain ⟨τ, hτ⟩ := fixed_incL I v hv (α + sigV I v α) (by rw [map_add, hinv, add_comm])
  by_cases hτi : τ ∈ v.adicCompletionIntegers I.F
  · exact ⟨τ, hτi, hτ⟩

  have key : ∀ r₀ : v.adicCompletion I.F, α = incL I v r₀ →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t := by
    rintro r₀ rfl
    have h1 : incL I v (r₀ * r₀) = incL I v 1 := by
      rw [map_mul, map_one, ← hα, sigV_incL]
    have hr0 : r₀ * r₀ = 1 := (incL I v).injective h1
    have hmem : r₀ ∈ v.adicCompletionIntegers I.F := by
      rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers I.F) r₀ with h | h
      · exact h
      · rwa [inv_eq_of_mul_eq_one_right hr0] at h
    exact ⟨r₀ + r₀, add_mem hmem hmem, by rw [sigV_incL, map_add]⟩
  have hdom : ∀ x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, x * y = 0 → x = 0 ∨ y = 0 := by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    · obtain ⟨b, hb⟩ := hv.mul_inv_cancel hx
      right
      calc y = (x * b) * y := by rw [hb, one_mul]
        _ = b * (x * y) := by ring
        _ = 0 := by rw [hxy, mul_zero]
  have hτinv : τ⁻¹ ∈ v.adicCompletionIntegers I.F :=
    (ValuationSubring.mem_or_inv_mem _ τ).resolve_left hτi
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact hτi (zero_mem _)
  set s : v.adicCompletionIntegers I.F := ⟨τ⁻¹ * τ⁻¹, mul_mem hτinv hτinv⟩ with hs
  have hsK : (s : v.adicCompletion I.F) = τ⁻¹ * τ⁻¹ := rfl
  have hsm : s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers I.F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hτi
    have h1 : ((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) * s = 1 := by
      rw [← hu, Units.inv_mul]
    have h3 := congrArg (v.adicCompletionIntegers I.F).subtype h1
    rw [map_mul, map_one] at h3
    change (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
      v.adicCompletion I.F) * (τ⁻¹ * τ⁻¹) = 1 at h3
    have hw : (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) = τ * τ := by
      field_simp at h3
      linear_combination h3
    have hτeq : τ = (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F) :
        v.adicCompletion I.F) * τ⁻¹ := by
      rw [hw]
      field_simp
    rw [hτeq]
    exact mul_mem (((u⁻¹ : (v.adicCompletionIntegers I.F)ˣ) : v.adicCompletionIntegers I.F)).2 hτinv
  haveI : HenselianLocalRing (v.adicCompletionIntegers I.F) := inferInstance
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian
    (Polynomial.X ^ 2 + (Polynomial.C s - Polynomial.X)) (by monicity!) 0
    (by simpa using hsm) (by simp)
  have ha2 : a ^ 2 + (s - a) = 0 := by simpa using ha
  have haK : (a : v.adicCompletion I.F) ^ 2 + (τ⁻¹ * τ⁻¹ - a) = 0 := by
    have h := congrArg (v.adicCompletionIntegers I.F).subtype ha2
    rw [map_add, map_pow, map_sub, map_zero] at h
    exact h
  have hr : (τ * a) * (τ - τ * a) = 1 := by
    have e1 : (a : v.adicCompletion I.F) - a ^ 2 = τ⁻¹ * τ⁻¹ := by linear_combination -haK
    calc (τ * a) * (τ - τ * a) = τ * τ * ((a : v.adicCompletion I.F) - a ^ 2) := by ring
      _ = τ * τ * (τ⁻¹ * τ⁻¹) := by rw [e1]
      _ = 1 := by field_simp
  have e2 : incL I v (τ * a) * incL I v (τ - τ * a) = 1 := by
    rw [← map_mul, hr, map_one]
  have e3 : incL I v (τ * a) + incL I v (τ - τ * a) = α + sigV I v α := by
    rw [← map_add, show τ * a + (τ - τ * a) = τ by ring, hτ]
  have hprod : (α - incL I v (τ * a)) * (α - incL I v (τ - τ * a)) = 0 := by
    linear_combination (-α) * e3 + e2 - hα
  rcases hdom _ _ hprod with h | h
  · exact key _ (sub_eq_zero.1 h)
  · exact key _ (sub_eq_zero.1 h)
end PI.UnitaryGroupMassFormula.AdIndexEq
