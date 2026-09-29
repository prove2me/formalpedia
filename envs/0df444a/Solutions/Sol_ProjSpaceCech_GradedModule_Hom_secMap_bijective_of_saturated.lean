-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a2dd2910-71cd-5b49-9141-f91183f0b913

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_Hom_secMap_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "GradedModule GradedModule.monMul GradedModule.monMul_add_apply GradedModule.monMul_single GradedModule.Frac GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.Hom GradedModule.Hom.secMap GradedModule.Hom.secMap_injective"
p2m_open "ProjSpaceCech"

section SecMapSat

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "monMul monMul_add_apply monMul_single Frac sec sec.mk sec_mk_eq Hom Hom.secMap mk xMul grade Hom.secMap_injective" namespace Hom p2m_export "ProjSpaceCech.GradedModule.Hom" "secMap mem_grade mk toLinearMap secMap_injective" end GradedModule.Hom
p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in
theorem GradedModule.Hom.secMap_mk (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
      = GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩ := rfl

p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.secMap_surjective_of_saturated (φ : GradedModule.Hom D₁ D₂)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Surjective (GradedModule.Hom.secMap φ I) := by
  classical
  obtain ⟨j, hj⟩ := hI
  intro q
  obtain ⟨⟨a, ha, m, hm⟩, rfl⟩ := Quotient.exists_rep q
  obtain ⟨k, m', hm', hφ⟩ := hsat j _ m hm
  let b : Fin (n + 1) → ℕ := a + Pi.single j k
  have hb : ∀ l, b l = a l + (Pi.single j k : Fin (n + 1) → ℕ) l := fun l => rfl
  have ha' : ∀ l ∉ I, b l = 0 := fun l hl => by
    have hlj : l ≠ j := fun h => hl (h ▸ hj)
    rw [hb, ha l hl, Pi.single_eq_of_ne hlj, add_zero]
  have hsum : (∑ l, (b l : ℤ)) = (∑ l, (a l : ℤ)) + k := by
    simp only [hb, Nat.cast_add, Finset.sum_add_distrib, add_right_inj]
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, Nat.cast_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
  refine ⟨GradedModule.sec.mk D₁ I ⟨b, ha', m', by rw [hsum]; exact hm'⟩, ?_⟩
  rw [GradedModule.Hom.secMap_mk]
  refine (GradedModule.sec_mk_eq D₂ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
  change GradedModule.monMul D₂ (0 + a) (φ.toLinearMap m') = GradedModule.monMul D₂ (0 + b) m
  rw [zero_add, zero_add, hφ, show b = a + Pi.single j k from rfl, GradedModule.monMul_add_apply,
    GradedModule.monMul_single]

p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.secMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Bijective (GradedModule.Hom.secMap φ I) :=
  ⟨GradedModule.Hom.secMap_injective φ hinj I, GradedModule.Hom.secMap_surjective_of_saturated φ hsat I hI⟩

end SecMapSat

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated' φ hinj hsat I hI

end

end S_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated (solution)
