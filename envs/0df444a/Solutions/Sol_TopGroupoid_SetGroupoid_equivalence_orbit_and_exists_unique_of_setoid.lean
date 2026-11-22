-- Prove2me | solution 1 for TopGroupoid.SetGroupoid.equivalence_orbit_and_exists_unique_of_setoid
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:42:18.416094+00:00
-- url     : https://prove2.me/submissions/faac1e72-2f37-48eb-8849-6e3cd918546d

import Definitions.Def_TopGroupoid_TopologicalGroupoid

set_option autoImplicit false

universe u v v'

namespace Sol_TopGroupoid_SetGroupoid_equivalence_orbit_and_exists_unique_of_setoid

open TopGroupoid

/-- Composites of equal composable pairs are equal. -/
theorem cc {X : Type u} {R : Type v} (G : SetGroupoid X R) {g g' h h' : R} (hg : g = g')
    (hh : h = h') (H : G.src g = G.tgt h) (H' : G.src g' = G.tgt h') :
    G.comp ⟨(g, h), H⟩ = G.comp ⟨(g', h'), H'⟩ := by subst hg hh; rfl

/-- An idempotent arrow of a groupoid is a unit. -/
theorem idem_unit {X : Type u} {R : Type v} (G : SetGroupoid X R) (a : R)
    (H : G.src a = G.tgt a) (h : G.comp ⟨(a, a), H⟩ = a) : a = G.unit (G.tgt a) := by
  have e1 : G.comp ⟨(a, G.inv a), (G.tgt_inv a).symm⟩ = G.unit (G.tgt a) := G.comp_inv a
  calc a = G.comp ⟨(a, G.unit (G.src a)), (G.tgt_unit _).symm⟩ := (G.comp_unit a).symm
    _ = G.comp ⟨(a, G.comp ⟨(a, G.inv a), (G.tgt_inv a).symm⟩),
          H.trans (G.tgt_comp ⟨(a, G.inv a), (G.tgt_inv a).symm⟩).symm⟩ :=
        cc G rfl (by rw [e1, H]) _ _
    _ = G.comp ⟨(G.comp ⟨(a, a), H⟩, G.inv a),
          (G.src_comp ⟨(a, a), H⟩).trans (G.tgt_inv a).symm⟩ :=
        G.comp_assoc a a (G.inv a) H (G.tgt_inv a).symm
    _ = G.comp ⟨(a, G.inv a), (G.tgt_inv a).symm⟩ := cc G h rfl _ _
    _ = G.unit (G.tgt a) := e1

/-- A map of arrows compatible with source, target and composition (over the identity of
objects) is a morphism of groupoids: units and inverses are preserved automatically. -/
theorem isHom_of_comp {X : Type u} {R : Type v} {R' : Type v'}
    (G : SetGroupoid X R) (G' : SetGroupoid X R') (f₂ : R → R')
    (hs : ∀ g : R, G'.src (f₂ g) = id (G.src g)) (ht : ∀ g : R, G'.tgt (f₂ g) = id (G.tgt g))
    (hc : ∀ (g h : R) (hgh : G.src g = G.tgt h),
          f₂ (G.comp ⟨(g, h), hgh⟩) =
            G'.comp ⟨(f₂ g, f₂ h), (hs g).trans ((congrArg id hgh).trans (ht h).symm)⟩) :
    G.IsHom G' id f₂ := by
  have hunit : ∀ x : X, f₂ (G.unit x) = G'.unit (id x) := by
    intro x
    have H : G'.src (f₂ (G.unit x)) = G'.tgt (f₂ (G.unit x)) := by
      rw [hs, ht, G.src_unit, G.tgt_unit]
    have hid : G'.comp ⟨(f₂ (G.unit x), f₂ (G.unit x)), H⟩ = f₂ (G.unit x) := by
      have h0 : G.src (G.unit x) = G.tgt (G.unit x) := by rw [G.src_unit, G.tgt_unit]
      rw [← hc (G.unit x) (G.unit x) h0]
      congr 1
      calc G.comp ⟨(G.unit x, G.unit x), h0⟩
          = G.comp ⟨(G.unit x, G.unit (G.src (G.unit x))), (G.tgt_unit _).symm⟩ :=
            cc G rfl (by rw [G.src_unit]) _ _
        _ = G.unit x := G.comp_unit _
    have := idem_unit G' _ H hid
    rw [this, ht, G.tgt_unit]
  refine ⟨hs, ht, hc, hunit, ?_⟩
  intro g
  have hb1 : G'.src (f₂ (G.inv g)) = G'.tgt (f₂ g) := by rw [hs, ht, G.src_inv]
  have hb2 : G'.comp ⟨(f₂ (G.inv g), f₂ g), hb1⟩ = G'.unit (G'.src (f₂ g)) := by
    rw [← hc (G.inv g) g (G.src_inv g), G.inv_comp, hunit, hs]
  calc f₂ (G.inv g)
      = G'.comp ⟨(f₂ (G.inv g), G'.unit (G'.src (f₂ (G.inv g)))), (G'.tgt_unit _).symm⟩ :=
        (G'.comp_unit _).symm
    _ = G'.comp ⟨(f₂ (G.inv g), G'.comp ⟨(f₂ g, G'.inv (f₂ g)), (G'.tgt_inv _).symm⟩),
          hb1.trans (G'.tgt_comp ⟨(f₂ g, G'.inv (f₂ g)), (G'.tgt_inv _).symm⟩).symm⟩ :=
        cc G' rfl (by rw [G'.comp_inv, hb1]) _ _
    _ = G'.comp ⟨(G'.comp ⟨(f₂ (G.inv g), f₂ g), hb1⟩, G'.inv (f₂ g)),
          (G'.src_comp ⟨(f₂ (G.inv g), f₂ g), hb1⟩).trans (G'.tgt_inv _).symm⟩ :=
        G'.comp_assoc _ _ _ hb1 (G'.tgt_inv _).symm
    _ = G'.comp ⟨(G'.unit (G'.tgt (G'.inv (f₂ g))), G'.inv (f₂ g)), G'.src_unit _⟩ :=
        cc G' (by rw [hb2, G'.tgt_inv]) rfl _ _
    _ = G'.inv (f₂ g) := G'.unit_comp _

end Sol_TopGroupoid_SetGroupoid_equivalence_orbit_and_exists_unique_of_setoid

open TopGroupoid Sol_TopGroupoid_SetGroupoid_equivalence_orbit_and_exists_unique_of_setoid

theorem solution {X : Type u} :
    (∀ (R : Type v) (G : SetGroupoid X R),
        Equivalence (fun x y : X => ∃ g : R, G.tgt g = x ∧ G.src g = y)) ∧
      (∀ r : Setoid X, ∃ G : SetGroupoid X {p : X × X // r p.1 p.2},
        (∀ p : {p : X × X // r p.1 p.2}, G.tgt p = p.1.1) ∧
          ∀ p : {p : X × X // r p.1 p.2}, G.src p = p.1.2) ∧
      ∀ (R₁ : Type v) (R₂ : Type v') (G₁ : SetGroupoid X R₁) (G₂ : SetGroupoid X R₂),
        Function.Injective (fun g : R₁ => (G₁.tgt g, G₁.src g)) →
        Function.Injective (fun g : R₂ => (G₂.tgt g, G₂.src g)) →
        (∀ x y : X, (∃ g : R₁, G₁.tgt g = x ∧ G₁.src g = y) ↔
          ∃ g : R₂, G₂.tgt g = x ∧ G₂.src g = y) →
        ∃ φ : R₁ ≃ R₂, G₁.IsHom G₂ id φ := by
  refine ⟨fun R G => ⟨fun x => ⟨G.unit x, G.tgt_unit x, G.src_unit x⟩, ?_, ?_⟩, fun r => ?_, ?_⟩
  · rintro x y ⟨g, rfl, rfl⟩
    exact ⟨G.inv g, G.tgt_inv g, G.src_inv g⟩
  · rintro x y z ⟨g, rfl, hy⟩ ⟨h, hy', rfl⟩
    exact ⟨G.comp ⟨(g, h), hy.trans hy'.symm⟩, G.tgt_comp _, G.src_comp _⟩
  · refine ⟨{ src := fun p => p.1.2, tgt := fun p => p.1.1,
              comp := fun p => ⟨(p.1.1.1.1, p.1.2.1.2), r.trans p.1.1.2 (p.2 ▸ p.1.2.2)⟩,
              unit := fun x => ⟨(x, x), r.refl x⟩,
              inv := fun p => ⟨(p.1.2, p.1.1), r.symm p.2⟩,
              tgt_comp := fun _ => rfl, src_comp := fun _ => rfl,
              comp_assoc := fun _ _ _ _ _ => rfl,
              src_unit := fun _ => rfl, tgt_unit := fun _ => rfl,
              comp_unit := fun _ => rfl, unit_comp := fun _ => rfl,
              src_inv := fun _ => rfl, tgt_inv := fun _ => rfl,
              comp_inv := fun _ => rfl, inv_comp := fun _ => rfl }, fun _ => rfl, fun _ => rfl⟩
  · intro R₁ R₂ G₁ G₂ inj₁ inj₂ H
    have ex : ∀ g : R₁, ∃ g' : R₂, G₂.tgt g' = G₁.tgt g ∧ G₂.src g' = G₁.src g :=
      fun g => (H _ _).1 ⟨g, rfl, rfl⟩
    have ex' : ∀ g' : R₂, ∃ g : R₁, G₁.tgt g = G₂.tgt g' ∧ G₁.src g = G₂.src g' :=
      fun g => (H _ _).2 ⟨g, rfl, rfl⟩
    choose φ hφt hφs using ex
    choose ψ hψt hψs using ex'
    have hφψ : ∀ g', φ (ψ g') = g' := fun g' => inj₂ (by simp [hφt, hφs, hψt, hψs])
    have hψφ : ∀ g, ψ (φ g) = g := fun g => inj₁ (by simp [hφt, hφs, hψt, hψs])
    refine ⟨⟨φ, ψ, hψφ, hφψ⟩,
      isHom_of_comp G₁ G₂ φ (fun g => hφs g) (fun g => hφt g) (fun g h hgh => inj₂ ?_)⟩
    simp [hφt, hφs, G₁.tgt_comp, G₁.src_comp, G₂.tgt_comp, G₂.src_comp]
