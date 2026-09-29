-- Prove2me | solution 1 for Rep.exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5001bcc0-ef33-5632-b166-37abe54bf8f2

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit

set_option autoImplicit false

open CategoryTheory

namespace ExtPit

universe u

section H0

variable {k G : Type u} [CommRing k] [Group G]

noncomputable def vec {A : Rep.{u} k G} (x : groupCohomology A 0) : A :=
  ((groupCohomology.H0Iso A).hom x).1

lemma vec_mem {A : Rep.{u} k G} (x : groupCohomology A 0) : vec x ∈ A.ρ.invariants :=
  ((groupCohomology.H0Iso A).hom x).2

lemma vec_map {H : Type u} [Group H] (f : G →* H) {A : Rep.{u} k H} {B : Rep.{u} k G} (φ : Rep.res f A ⟶ B)
    (x : groupCohomology A 0) : vec (groupCohomology.map f φ 0 x) = φ.hom (vec (A := A) x) :=
  groupCohomology.map_H0Iso_hom_f_apply f φ x

lemma vec_injective {A : Rep.{u} k G} : Function.Injective (vec : groupCohomology A 0 → A) := by
  intro x y h
  have h1 : (groupCohomology.H0Iso A).hom x = (groupCohomology.H0Iso A).hom y := Subtype.ext h
  have h2 := congrArg (groupCohomology.H0Iso A).inv h1
  simpa using h2

lemma exists_vec_eq {A : Rep.{u} k G} (a : A) (ha : a ∈ A.ρ.invariants) : ∃ x : groupCohomology A 0, vec x = a :=
  ⟨(groupCohomology.H0Iso A).inv ⟨a, ha⟩, by simp [vec]⟩

end H0

section RepFacts

variable {k G : Type u} [CommRing k] [Group G]

def toLin {R X : Rep.{u} k G} (t : (ihom R).obj X) : R →ₗ[k] X := t

lemma toLin_ext {R X : Rep.{u} k G} {s t : (ihom R).obj X} (h : ∀ r : R, toLin s r = toLin t r) : s = t :=
  LinearMap.ext h

lemma apply_ρ_of_mem_invariants {R X : Rep.{u} k G} {t : (ihom R).obj X} (ht : t ∈ ((ihom R).obj X).ρ.invariants)
    (g : G) (r : R) : toLin t (R.ρ g r) = X.ρ g (toLin t r) := by
  have h := (Representation.linHom.mem_invariants_iff_comm (X := R) (Y := X) (toLin t) g).1 (ht g)
  exact LinearMap.congr_fun h r

lemma mem_invariants_of_apply_ρ {R X : Rep.{u} k G} (t : (ihom R).obj X)
    (ht : ∀ (g : G) (r : R), toLin t (R.ρ g r) = X.ρ g (toLin t r)) :
    t ∈ ((ihom R).obj X).ρ.invariants :=
  fun g => (Representation.linHom.mem_invariants_iff_comm (X := R) (Y := X) (toLin t) g).2 (LinearMap.ext (ht g))

lemma injective_of_shortExact {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) : Function.Injective S.f.hom :=
  (Rep.mono_iff_injective S.f).1 hS.mono_f

lemma exists_of_shortExact {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (y : S.X₂) (hy : S.g.hom y = 0) :
    ∃ x : S.X₁, S.f.hom x = y := by
  have h := (hS.map_of_exact (forget₂ (Rep.{u} k G) (ModuleCat.{u} k))).exact
  rw [ShortComplex.moduleCat_exact_iff] at h
  exact h y hy

lemma comp_hom_apply {X Y Z : Rep.{u} k G} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

lemma hom_apply_eq_of_comp_eq {X Y Y' Z : Rep.{u} k G} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z}
    (w : f ≫ g = f' ≫ g') (x : X) : g.hom (f.hom x) = g'.hom (f'.hom x) := by
  rw [← comp_hom_apply, ← comp_hom_apply, w]

end RepFacts

section Chase

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G) (B : Rep.{u} k G) (p : ℕ)
  (hB : ∀ b : B, p • b = 0)
  (T : ShortComplex (Rep.{u} k G)) {T' : ShortComplex (Rep.{u} k G')} (hT' : T'.ShortExact)
  (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
  (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
  (hpit : ∀ c : T.X₃, (∃ n : ℕ, p ^ n • c = 0) → φ₃.hom c = 0)
  (ψ : (ihom (Rep.free k G B)).obj T.X₂) (hψ : ψ ∈ ((ihom (Rep.free k G B)).obj T.X₂).ρ.invariants)
  (hker : ∀ u : Rep.free k G B, (Rep.freeCover B).hom u = 0 → T.g.hom (toLin ψ u) = 0)

include hB hker in

lemma smul_g_ψ_eq_zero (u : Rep.free k G B) : p • T.g.hom (toLin ψ u) = 0 := by
  rw [← map_nsmul, ← map_nsmul]
  apply hker
  rw [map_nsmul]
  exact hB _

include hB hker w₂ hpit in

lemma g'_φ₂_ψ_eq_zero (u : Rep.free k G B) : T'.g.hom (φ₂.hom (toLin ψ u)) = 0 := by
  rw [← hom_apply_eq_of_comp_eq w₂]
  exact hpit _ ⟨1, by rw [pow_one]; exact smul_g_ψ_eq_zero B p hB T ψ hker u⟩

include hB hker w₂ hpit hψ hT' in

theorem exists_mem_invariants_forall_f_apply_eq :
    ∃ W : (ihom (Rep.free k G' (Rep.res π B))).obj T'.X₁, W ∈ ((ihom (Rep.free k G' (Rep.res π B))).obj T'.X₁).ρ.invariants ∧
      ∀ x : Rep.free k G' (Rep.res π B), T'.f.hom (toLin W x) = φ₂.hom (toLin ψ ((Rep.freeResMap π B).hom x)) := by
  have hinj := injective_of_shortExact hT'

  choose w hw using fun u : Rep.free k G B =>
    exists_of_shortExact hT' (φ₂.hom (toLin ψ u)) (g'_φ₂_ψ_eq_zero π B p hB T φ₂ φ₃ w₂ hpit ψ hker u)
  have w_add : ∀ u v, w (u + v) = w u + w v := fun u v => hinj (by rw [hw, map_add, map_add, map_add, hw, hw])
  have w_smul : ∀ (c : k) u, w (c • u) = c • w u := fun c u => hinj (by rw [hw, map_smul, map_smul, map_smul, hw])
  have w_ρ : ∀ (g : G') u, w ((Rep.free k G B).ρ (π g) u) = T'.X₁.ρ g (w u) := fun g u => hinj (by
    rw [hw, apply_ρ_of_mem_invariants hψ (π g) u, Rep.hom_comm_apply T'.f g, hw]
    exact Rep.hom_comm_apply φ₂ g (toLin ψ u))

  let w₀ : Rep.res π (Rep.free k G B) →ₗ[k] T'.X₁ := { toFun := w, map_add' := w_add, map_smul' := w_smul }
  refine ⟨(show (Rep.free k G' (Rep.res π B)) →ₗ[k] T'.X₁ from w₀ ∘ₗ (Rep.freeResMap π B).hom.toLinearMap), ?_,
    fun x => hw _⟩
  apply mem_invariants_of_apply_ρ
  intro g x
  change w ((Rep.freeResMap π B).hom ((Rep.free k G' (Rep.res π B)).ρ g x)) = T'.X₁.ρ g (w ((Rep.freeResMap π B).hom x))
  rw [← w_ρ]
  exact congrArg w (Rep.hom_comm_apply (Rep.freeResMap π B) g x)

end Chase

end ExtPit

theorem solution
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (z : groupCohomology ((ihom (Rep.relationModuleInt B)).obj T.X₁) 0)
    (hz : ∃ ψ : groupCohomology ((ihom (Rep.free ℤ G B)).obj T.X₂) 0,
      (groupCohomology.map (MonoidHom.id G) (Rep.preι B T.X₂) 0).hom ψ =
        (groupCohomology.map (MonoidHom.id G) ((ihom (Rep.relationModuleInt B)).map T.f) 0).hom z) :
    ∃ ψ' : groupCohomology ((ihom (Rep.free ℤ G' (Rep.res π B))).obj T'.X₁) 0,
      (groupCohomology.map (MonoidHom.id G') (Rep.preι (Rep.res π B) T'.X₁) 0).hom ψ' =
        (groupCohomology.map π (Rep.extInflR π B T.X₁ T'.X₁ φ₁) 0).hom z := by
  have _ := hT

  obtain ⟨ψ, hψ⟩ := hz
  have e₁ := ExtPit.vec_map (MonoidHom.id G) (Rep.preι B T.X₂) ψ
  have e₂ := ExtPit.vec_map (MonoidHom.id G) ((ihom (Rep.relationModuleInt B)).map T.f) z
  have hψv : (Rep.preι B T.X₂).hom (ExtPit.vec ψ) = ((ihom (Rep.relationModuleInt B)).map T.f).hom (ExtPit.vec z) := by
    rw [← e₁, ← e₂]
    exact congrArg ExtPit.vec hψ
  have hψr : ∀ r : Rep.relationModuleInt B,
      ExtPit.toLin (ExtPit.vec ψ) ((Rep.relationModuleInt.ι B).hom r) = T.f.hom (ExtPit.toLin (ExtPit.vec z) r) := fun r =>
    congrArg (fun t : (ihom (Rep.relationModuleInt B)).obj T.X₂ => ExtPit.toLin t r) hψv
  have hker : ∀ u : Rep.free ℤ G B, (Rep.freeCover B).hom u = 0 → T.g.hom (ExtPit.toLin (ExtPit.vec ψ) u) = 0 := by
    intro u hu
    have h := hψr (show Rep.relationModule B from ⟨u, hu⟩)
    change ExtPit.toLin (ExtPit.vec ψ) u = _ at h
    rw [h, ← ExtPit.comp_hom_apply, T.zero, Rep.zero_hom]
    rfl

  obtain ⟨W, hWinv, hW⟩ := ExtPit.exists_mem_invariants_forall_f_apply_eq π B p hB T hT' φ₂ φ₃ w₂ hpit
    (ExtPit.vec ψ) (ExtPit.vec_mem ψ) hker

  obtain ⟨ψ', hψ'⟩ := ExtPit.exists_vec_eq W hWinv
  refine ⟨ψ', ExtPit.vec_injective ?_⟩
  rw [ExtPit.vec_map (MonoidHom.id G') (Rep.preι (Rep.res π B) T'.X₁) ψ',
    ExtPit.vec_map π (Rep.extInflR π B T.X₁ T'.X₁ φ₁) z, hψ']
  refine ExtPit.toLin_ext fun r' => ?_
  change ExtPit.toLin W ((Rep.relationModuleInt.ι (Rep.res π B)).hom r') =
    φ₁.hom (ExtPit.toLin (ExtPit.vec z) ((Rep.relationModuleInt.resMap π B).hom r'))
  apply ExtPit.injective_of_shortExact hT'
  rw [hW, ← ExtPit.hom_apply_eq_of_comp_eq w₁]
  change φ₂.hom (ExtPit.toLin (ExtPit.vec ψ) ((Rep.relationModuleInt.ι B).hom ((Rep.relationModuleInt.resMap π B).hom r'))) =
    φ₂.hom (T.f.hom (ExtPit.toLin (ExtPit.vec z) ((Rep.relationModuleInt.resMap π B).hom r')))
  rw [hψr]

end S_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
end P2MW
export P2MW.S_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit (solution)
