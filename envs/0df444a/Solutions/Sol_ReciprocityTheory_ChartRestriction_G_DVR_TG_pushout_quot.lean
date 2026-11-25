-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.pushout_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:10.433078+00:00
-- url     : https://prove2.me/submissions/59436025-7a5c-4d94-ad5e-aabc58b4fc1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {R A B P : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {c : A ⟶ P} {d : B ⟶ P}
    (h : IsPushout a b c d) (hb : Function.Surjective b) :
    Function.Surjective c ∧ ∀ x, c x = 0 → x ∈ (RingHom.ker b.hom).map a.hom := by
  set J := RingHom.ker b.hom
  let Q := CommRingCat.of (A ⧸ J.map a.hom)
  let mk : A ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hker : RingHom.ker b.hom ≤ RingHom.ker ((Ideal.Quotient.mk (J.map a.hom)).comp a.hom) := by
    intro r hr
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  let bQ : B ⟶ Q := CommRingCat.ofHom (RingHom.liftOfSurjective b.hom hb ⟨_, hker⟩)
  have hbQ : ∀ r, bQ (b r) = mk (a r) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  have comm : a ≫ mk = b ≫ bQ := by
    ext r; exact (hbQ r).symm
  let hQ : P ⟶ Q := h.desc mk bQ comm
  have h1 : c ≫ hQ = mk := h.inl_desc _ _ _
  have h2 : d ≫ hQ = bQ := h.inr_desc _ _ _
  have hc : J.map a.hom ≤ RingHom.ker c.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun φ => φ.hom r) h.w
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this, show b.hom r = 0 from hr, map_zero]
  let k : Q ⟶ P := CommRingCat.ofHom (Ideal.Quotient.lift _ c.hom hc)
  have hmk : mk ≫ k = c := by ext x; rfl
  have hid : hQ ≫ k = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, hmk, Category.comp_id]
    · rw [← Category.assoc, h2, Category.comp_id]
      ext y
      obtain ⟨r, rfl⟩ := hb y
      have e1 : k (bQ (b r)) = c (a r) := by rw [hbQ]; rfl
      have e2 := congrArg (fun φ => φ.hom r) h.w
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
      simpa using e1.trans e2
  refine ⟨fun p => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (hQ p)
    refine ⟨x, ?_⟩
    have : k (hQ p) = p := by
      have := congrArg (fun φ => φ.hom p) hid; simpa using this
    rw [← this, ← hx]; rfl
  · have : mk x = hQ (c x) := by rw [← h1]; rfl
    rw [hx, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
end ReciprocityTheory.ChartRestriction.G.DVR.TG
