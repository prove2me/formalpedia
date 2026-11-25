-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_length_quot_eq_relfinrank_5f604ca6cb09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:26:18.893833+00:00
-- url     : https://prove2.me/submissions/aef8f45f-b829-47b8-bed5-6d80c314889b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_ab88e3b42d04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
theorem _root_.solution {F : Type} [Field F] [Algebra F Ω] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔪 : Ideal B) (ρ : B →+* Ω) (hker : ∀ b, ρ b = 0 ↔ b ∈ 𝔪)
    (L₀ L : IntermediateField F Ω) (hle : L₀ ≤ L) (hB : ∀ b, ρ b ∈ L) (hBs : ∀ y ∈ L, ∃ b, ρ b = y)
    (hA : ∀ a, ρ (algebraMap A B a) ∈ L₀) (hAs : ∀ y ∈ L₀, ∃ a, ρ (algebraMap A B a) = y) :
    Module.length A (B ⧸ 𝔪) = (IntermediateField.relfinrank L₀ L : ℕ∞) := by
  set E := IntermediateField.extendScalars hle with hE
  let ψA : A →+* L₀ := (ρ.comp (algebraMap A B)).codRestrict L₀ hA
  let ψB : B →+* E := ρ.codRestrict E hB
  have hψA : Function.Surjective ψA := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hAs y hy
    exact ⟨a, Subtype.ext ha⟩
  have hψB : Function.Surjective ψB := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ := hBs y hy
    exact ⟨b, Subtype.ext hb⟩
  let _ : Algebra A L₀ := ψA.toAlgebra
  let _ : Algebra A E := ((algebraMap L₀ E).comp ψA).toAlgebra
  have : IsScalarTower A L₀ E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hkerψ : RingHom.ker ψB = 𝔪 := by
    ext b
    rw [RingHom.mem_ker, ← hker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hH : ∀ b ∈ 𝔪, ψB b = 0 := fun b hb => by
    rw [← hkerψ] at hb
    exact hb
  let φ := Ideal.Quotient.lift 𝔪 ψB hH
  let φl : (B ⧸ 𝔪) →ₗ[A] E :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := by
        intro a m
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, RingHom.id_apply, Algebra.smul_def]
        apply Subtype.ext
        show ρ (algebraMap A B a * b) = ρ (algebraMap A B a) * ρ b
        exact map_mul ρ _ _ }
  have hφ : Function.Bijective φl :=
    ⟨(Ideal.injective_lift_iff hH).2 hkerψ, fun y => by
      obtain ⟨b, hb⟩ := hψB y
      exact ⟨Ideal.Quotient.mk 𝔪 b, hb⟩⟩
  let φe := LinearEquiv.ofBijective φl hφ
  have : Module.Finite A (B ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite A E := Module.Finite.equiv φe
  have : Module.Finite L₀ E := Module.Finite.of_restrictScalars_finite A L₀ E
  rw [φe.length_eq, Module.length_eq_of_surjective (R := L₀) hψA, Module.length_eq_finrank,
    IntermediateField.relfinrank_eq_finrank_of_le hle]
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
