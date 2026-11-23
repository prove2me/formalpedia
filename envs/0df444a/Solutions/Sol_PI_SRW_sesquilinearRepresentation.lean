-- Prove2me | solution 1 for PI.SRW.sesquilinearRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:42.215647+00:00
-- url     : https://prove2.me/submissions/27a95169-0ca0-4a26-8142-9af28c70b0d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_CoordStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_SesquilinearRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open PI PI.SRW
namespace PI.SRW
theorem _root_.solution : RepStep := by
  intro E V _ _ _ _ _ _ _ _ h hnd Λ hΛ ℓ

  have hsurj : Function.Surjective h := by
    rw [← LinearMap.range_eq_top]
    have hco : (LinearMap.range h).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_dualCoannihilator] at hy
      rw [Submodule.mem_bot]
      exact hnd.2 y (fun x => hy (h x) ⟨x, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h), hco,
      Submodule.dualAnnihilator_bot]

  obtain ⟨s, hsΛ, hspan, hli⟩ := exists_linearIndependent E (Λ : Set V)
  have hs_top : Submodule.span E s = ⊤ := hspan.trans hΛ.span_eq_top
  let b : Basis s E V := Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hs_top]))
  let φ : V →ₗ[E] E := b.constr E (fun i => ℓ ⟨i.1, hsΛ i.2⟩)
  have hφb : ∀ v (hv : v ∈ s), φ v = ℓ ⟨v, hsΛ hv⟩ := by
    intro v hv
    have hb : b ⟨v, hv⟩ = v := Basis.mk_apply _ _ _
    have e := b.constr_basis E (fun i : s => ℓ ⟨i.1, hsΛ i.2⟩) ⟨v, hv⟩
    rw [hb] at e
    exact e

  have hind : ∀ y ∈ Submodule.span (𝓞 E) (s : Set V), ∃ hy : y ∈ Λ, ℓ ⟨y, hy⟩ = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem v hv => exact ⟨hsΛ hv, (hφb v hv).symm⟩
    | zero => exact ⟨zero_mem _, (map_zero ℓ).trans (map_zero φ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨hu', eu⟩ := hu
      obtain ⟨hv', ev⟩ := hv
      refine ⟨add_mem hu' hv', ?_⟩
      have e : (⟨u + v, add_mem hu' hv'⟩ : Λ) = ⟨u, hu'⟩ + ⟨v, hv'⟩ := rfl
      rw [e, map_add, map_add, eu, ev]
    | smul a u _ hu =>
      obtain ⟨hu', eu⟩ := hu
      refine ⟨Λ.smul_mem a hu', ?_⟩
      have e : (⟨a • u, Λ.smul_mem a hu'⟩ : Λ) = a • ⟨u, hu'⟩ := rfl
      rw [e, map_smul, eu, ← algebraMap_smul E a u, map_smul, Algebra.smul_def, smul_eq_mul]

  have key : ∀ x : Λ, φ x = ℓ x := by
    intro x
    have hxE : (x : V) ∈ Submodule.span E s := by
      rw [hs_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hxy⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).mp hxE
    have hzx : (z : 𝓞 E) • (x : V) = y := by
      rw [hxy, ← algebraMap_smul E (z : 𝓞 E), smul_smul, IsLocalization.mk'_spec', map_one,
        one_smul]
    obtain ⟨hyΛ, hℓφ⟩ := hind y hy
    have h1 : ℓ ((z : 𝓞 E) • x) = algebraMap (𝓞 E) E z * ℓ x := by
      rw [map_smul, Algebra.smul_def]
    have h2 : φ ((z : 𝓞 E) • (x : V)) = algebraMap (𝓞 E) E z * φ x := by
      rw [← algebraMap_smul E (z : 𝓞 E) (x : V), map_smul, smul_eq_mul]
    have hzΛ : ((z : 𝓞 E) • x : Λ) = ⟨y, hyΛ⟩ := by
      ext
      exact hzx
    have hne : algebraMap (𝓞 E) E z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    apply mul_left_cancel₀ hne
    rw [← h1, ← h2, hzΛ, hzx, hℓφ]
  obtain ⟨w, hw⟩ := hsurj φ
  exact ⟨w, fun x => by rw [hw, key]⟩
end PI.SRW
