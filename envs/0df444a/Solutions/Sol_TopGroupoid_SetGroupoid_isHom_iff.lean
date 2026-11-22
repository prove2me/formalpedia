-- Prove2me | solution 1 for TopGroupoid.SetGroupoid.isHom_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:38:19.664967+00:00
-- url     : https://prove2.me/submissions/5efd300f-7018-4f24-97b7-62ab033a3c63

import Definitions.Def_TopGroupoid_TopologicalGroupoid

set_option autoImplicit false

universe u v u' v'

namespace Sol_TopGroupoid_SetGroupoid_isHom_iff

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

end Sol_TopGroupoid_SetGroupoid_isHom_iff

open TopGroupoid Sol_TopGroupoid_SetGroupoid_isHom_iff

theorem solution {X : Type u} {R : Type v} {X' : Type u'} {R' : Type v'}
    (G : SetGroupoid X R) (G' : SetGroupoid X' R') (f₁ : X → X') (f₂ : R → R') :
    G.IsHom G' f₁ f₂ ↔
      ∃ (hs : ∀ g : R, G'.src (f₂ g) = f₁ (G.src g)) (ht : ∀ g : R, G'.tgt (f₂ g) = f₁ (G.tgt g)),
        ∀ (g h : R) (hgh : G.src g = G.tgt h),
          f₂ (G.comp ⟨(g, h), hgh⟩) =
            G'.comp ⟨(f₂ g, f₂ h), (hs g).trans ((congrArg f₁ hgh).trans (ht h).symm)⟩ := by
  constructor
  · intro H
    exact ⟨H.map_src, H.map_tgt, H.map_comp⟩
  · rintro ⟨hs, ht, hc⟩
    have hunit : ∀ x : X, f₂ (G.unit x) = G'.unit (f₁ x) := by
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
