-- Prove2me | solution 1 for RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/03343249-39d4-545d-b56c-8c96b829ad8e

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
import Theorems.Thm_Algebra_FinitePresentation_of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace AlphaFlatTriple

variable {B B₁ : Type} [CommRing B] [CommRing B₁] {A₁ A₀ : Type} [CommRing A₁] [CommRing A₀]

theorem surjective_of_isPushout (φ : B₁ →+* B) (a₁ : B₁ →+* A₁) (a₀ : B →+* A₀) (g : A₁ →+* A₀)
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom a₁) (CommRingCat.ofHom a₀) (CommRingCat.ofHom g))
    (hφ : Function.Surjective φ) : Function.Surjective g := by
  have hw : ∀ b, a₀ (φ b) = g (a₁ b) := fun b => by
    have := congrArg (fun f => CommRingCat.Hom.hom f b) H.w
    simpa using this
  let S : Subring A₀ := g.range
  have hS : ∀ b, a₀ b ∈ S := fun b => by
    obtain ⟨b₁, rfl⟩ := hφ b
    exact ⟨a₁ b₁, (hw b₁).symm⟩
  let uB : B →+* S := a₀.codRestrict S hS
  let uA : A₁ →+* S := g.rangeRestrict
  have hc : CommRingCat.ofHom φ ≫ CommRingCat.ofHom uB = CommRingCat.ofHom a₁ ≫ CommRingCat.ofHom uA := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro b; apply Subtype.ext
    show a₀ (φ b) = g (a₁ b)
    exact hw b
  let w := H.desc (CommRingCat.ofHom uB) (CommRingCat.ofHom uA) hc
  have h1 : CommRingCat.ofHom a₀ ≫ (w ≫ CommRingCat.ofHom S.subtype) = CommRingCat.ofHom a₀ ≫ 𝟙 _ := by
    rw [← Category.assoc, H.inl_desc]; rfl
  have h2 : CommRingCat.ofHom g ≫ (w ≫ CommRingCat.ofHom S.subtype) = CommRingCat.ofHom g ≫ 𝟙 _ := by
    rw [← Category.assoc, H.inr_desc]; rfl
  have hid := H.hom_ext h1 h2
  intro y
  have hy : S.subtype (w.hom y) = y := by
    have := congrArg (fun f => CommRingCat.Hom.hom f y) hid
    simpa using this
  rw [← hy]
  exact (w.hom y).2

theorem ker_le_map_of_isPushout (φ : B₁ →+* B) (a₁ : B₁ →+* A₁) (a₀ : B →+* A₀) (g : A₁ →+* A₀)
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom a₁) (CommRingCat.ofHom a₀) (CommRingCat.ofHom g))
    (hφ : Function.Surjective φ) : RingHom.ker g ≤ (RingHom.ker φ).map a₁ := by
  have hw : ∀ b, a₀ (φ b) = g (a₁ b) := fun b => by
    have := congrArg (fun f => CommRingCat.Hom.hom f b) H.w
    simpa using this
  set J : Ideal A₁ := (RingHom.ker φ).map a₁ with hJ

  let e : (B₁ ⧸ RingHom.ker φ) ≃+* B :=
    RingEquiv.ofBijective (RingHom.kerLift φ) ⟨RingHom.kerLift_injective φ, fun b => by
      obtain ⟨b₁, rfl⟩ := hφ b; exact ⟨Ideal.Quotient.mk _ b₁, RingHom.kerLift_mk φ b₁⟩⟩
  have he : ∀ b₁, e.symm (φ b₁) = Ideal.Quotient.mk _ b₁ := fun b₁ => by
    apply e.injective; rw [e.apply_symm_apply]; exact (RingHom.kerLift_mk φ b₁).symm
  let l : (B₁ ⧸ RingHom.ker φ) →+* (A₁ ⧸ J) :=
    Ideal.Quotient.lift (RingHom.ker φ) ((Ideal.Quotient.mk J).comp a₁) (fun k hk => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem a₁ hk)
  let uB : B →+* (A₁ ⧸ J) := l.comp e.symm.toRingHom
  have hc : CommRingCat.ofHom φ ≫ CommRingCat.ofHom uB = CommRingCat.ofHom a₁ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro b
    show l (e.symm (φ b)) = Ideal.Quotient.mk J (a₁ b)
    rw [he]
    rfl
  let w := H.desc (CommRingCat.ofHom uB) (CommRingCat.ofHom (Ideal.Quotient.mk J)) hc
  have hwg : ∀ x, w.hom (g x) = Ideal.Quotient.mk J x := fun x =>
    congrArg (fun f => CommRingCat.Hom.hom f x) (H.inr_desc (CommRingCat.ofHom uB) (CommRingCat.ofHom (Ideal.Quotient.mk J)) hc)
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hwg, hx, map_zero]

end AlphaFlatTriple

namespace AlphaFlatTriple

section Squares

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B)
  {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
  (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
  (a : pullbackRing φ' φ'' →+* pullbackRing g' g'')

theorem isPushout_fst
    (hφ''s : Function.Surjective φ'') (hg's : Function.Surjective g') (hg''s : Function.Surjective g'')
    (hw'' : ∀ b, a₀ (φ'' b) = g'' (a'' b))
    (hker'' : RingHom.ker g'' ≤ (RingHom.ker φ'').map a'')
    (ha' : (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ''))
    (ha'' : (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'')) :
    IsPushout (CommRingCat.ofHom (pullbackFst φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a')
      (CommRingCat.ofHom (pullbackFst g' g'')) := by
  classical
  have ha'x : ∀ x, pullbackFst g' g'' (a x) = a' (pullbackFst φ' φ'' x) := fun x => RingHom.congr_fun ha' x
  have ha''x : ∀ x, pullbackSnd g' g'' (a x) = a'' (pullbackSnd φ' φ'' x) := fun x => RingHom.congr_fun ha'' x
  have hcond : CommRingCat.ofHom (pullbackFst φ' φ'') ≫ CommRingCat.ofHom a' =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (pullbackFst g' g'') := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha']

  have hsA : Function.Surjective (pullbackFst g' g'') := fun x' => by
    obtain ⟨x'', hx''⟩ := hg''s (g' x')
    exact ⟨⟨(x', x''), show g' x' = g'' x'' from hx''.symm⟩, rfl⟩

  have hkill : ∀ (T : Type) [CommRing T] (u : B' →+* T) (v : pullbackRing g' g'' →+* T),
      (∀ x, u (pullbackFst φ' φ'' x) = v (a x)) →
      ∀ z : pullbackRing g' g'', pullbackFst g' g'' z = 0 → v z = 0 := by
    intro T _ u v huv z hz
    have hz1 : z.1.1 = 0 := hz
    have hy : z.1.2 ∈ RingHom.ker g'' := by
      rw [RingHom.mem_ker]
      have hz2 : g' z.1.1 = g'' z.1.2 := z.2
      rw [← hz2, hz1, map_zero]
    have hyJ := hker'' hy

    have main : ∀ y ∈ (RingHom.ker φ'').map a'',
        ∃ hm : ((0 : A'), y) ∈ pullbackRing g' g'', v ⟨((0 : A'), y), hm⟩ = 0 := by
      intro y hy'
      rw [Ideal.map] at hy'
      induction hy' using Submodule.span_induction with
      | mem y hy0 =>
          obtain ⟨k, hk, rfl⟩ := hy0
          have hk0 : φ'' k = 0 := hk
          have hm : ((0 : A'), a'' k) ∈ pullbackRing g' g'' := by
            show g' 0 = g'' (a'' k)
            rw [map_zero, ← hw'', hk0, map_zero]
          refine ⟨hm, ?_⟩
          let pk : pullbackRing φ' φ'' := ⟨((0 : B'), k), show φ' 0 = φ'' k by rw [map_zero, hk0]⟩
          have hapk : a pk = ⟨((0 : A'), a'' k), hm⟩ := by
            apply Subtype.ext
            apply Prod.ext
            · show pullbackFst g' g'' (a pk) = 0
              rw [ha'x]; show a' 0 = 0; exact map_zero a'
            · show pullbackSnd g' g'' (a pk) = a'' k
              rw [ha''x]; rfl
          rw [← hapk, ← huv]
          show u 0 = 0
          exact map_zero u
      | zero =>
          refine ⟨show g' 0 = g'' 0 by rw [map_zero, map_zero], ?_⟩
          have : (⟨((0 : A'), (0 : A'')), show g' 0 = g'' 0 by rw [map_zero, map_zero]⟩ : pullbackRing g' g'') = 0 := rfl
          rw [this, map_zero]
      | add y₁ y₂ _ _ h₁ h₂ =>
          obtain ⟨hm₁, hv₁⟩ := h₁
          obtain ⟨hm₂, hv₂⟩ := h₂
          have hm : ((0 : A'), y₁ + y₂) ∈ pullbackRing g' g'' := by
            have := (pullbackRing g' g'').add_mem hm₁ hm₂
            simpa using this
          refine ⟨hm, ?_⟩
          have : (⟨((0 : A'), y₁ + y₂), hm⟩ : pullbackRing g' g'') = ⟨((0 : A'), y₁), hm₁⟩ + ⟨((0 : A'), y₂), hm₂⟩ := by
            apply Subtype.ext; apply Prod.ext
            · show (0 : A') = 0 + 0; rw [add_zero]
            · rfl
          rw [this, map_add, hv₁, hv₂, add_zero]
      | smul r y _ h =>
          obtain ⟨hm, hv⟩ := h
          obtain ⟨r', hr'⟩ := hg's (g'' r)
          have hL : (r', r) ∈ pullbackRing g' g'' := show g' r' = g'' r from hr'
          have hm' : ((0 : A'), r • y) ∈ pullbackRing g' g'' := by
            have := (pullbackRing g' g'').mul_mem hL hm
            simpa [smul_eq_mul] using this
          refine ⟨hm', ?_⟩
          have : (⟨((0 : A'), r • y), hm'⟩ : pullbackRing g' g'') = ⟨(r', r), hL⟩ * ⟨((0 : A'), y), hm⟩ := by
            apply Subtype.ext; apply Prod.ext
            · show (0 : A') = r' * 0; rw [mul_zero]
            · show r • y = r * y; rfl
          rw [this, map_mul, hv, mul_zero]
    obtain ⟨hm, hv⟩ := main z.1.2 hyJ
    have hz' : z = ⟨((0 : A'), z.1.2), hm⟩ := by
      apply Subtype.ext; apply Prod.ext
      · exact hz1
      · rfl
    rw [hz']
    exact hv

  have key : ∀ (T : Type) [CommRing T] (u : B' →+* T) (v : pullbackRing g' g'' →+* T),
      (∀ x, u (pullbackFst φ' φ'' x) = v (a x)) →
      ∃ w : A' →+* T, (∀ z, w (pullbackFst g' g'' z) = v z) ∧ (∀ b, w (a' b) = u b) := by
    intro T _ u v huv
    have hv : ∀ z ∈ RingHom.ker (pullbackFst g' g''), v z = 0 := fun z hz => hkill T u v huv z hz
    let e : (pullbackRing g' g'' ⧸ RingHom.ker (pullbackFst g' g'')) ≃+* A' :=
      RingEquiv.ofBijective (RingHom.kerLift (pullbackFst g' g''))
        ⟨RingHom.kerLift_injective _, fun x' => by
          obtain ⟨z, rfl⟩ := hsA x'
          exact ⟨Ideal.Quotient.mk _ z, RingHom.kerLift_mk _ z⟩⟩
    have he : ∀ z, e.symm (pullbackFst g' g'' z) = Ideal.Quotient.mk _ z := fun z => by
      apply e.injective; rw [e.apply_symm_apply]; exact (RingHom.kerLift_mk _ z).symm
    let l : (pullbackRing g' g'' ⧸ RingHom.ker (pullbackFst g' g'')) →+* T :=
      Ideal.Quotient.lift _ v hv
    refine ⟨l.comp e.symm.toRingHom, fun z => ?_, fun b => ?_⟩
    · show l (e.symm (pullbackFst g' g'' z)) = v z
      rw [he]; rfl
    · obtain ⟨b'', hb''⟩ := hφ''s (φ' b)
      let pb : pullbackRing φ' φ'' := ⟨(b, b''), show φ' b = φ'' b'' from hb''.symm⟩
      have h1 : a' b = pullbackFst g' g'' (a pb) := by rw [ha'x]; rfl
      show l (e.symm (a' b)) = u b
      rw [h1, he]
      show v (a pb) = u b
      rw [← huv]; rfl
  refine IsPushout.of_isColimit' ⟨hcond⟩ ?_
  refine PushoutCocone.IsColimit.mk hcond
    (fun s => CommRingCat.ofHom (Classical.choose (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition)))) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext; apply RingHom.ext; intro b
    exact (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).2 b
  · intro s
    apply CommRingCat.hom_ext; apply RingHom.ext; intro z
    exact (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).1 z
  · intro s m hm₁ hm₂
    apply CommRingCat.hom_ext; apply RingHom.ext; intro x'
    obtain ⟨z, rfl⟩ := hsA x'
    have e1 := (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).1 z
    have e2 : m.hom (pullbackFst g' g'' z) = s.inr.hom z := congrArg (fun f => CommRingCat.Hom.hom f z) hm₂
    exact e2.trans e1.symm

end Squares

end AlphaFlatTriple

namespace AlphaFlatTriple

section SquaresSnd

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B)
  {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
  (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
  (a : pullbackRing φ' φ'' →+* pullbackRing g' g'')

theorem isPushout_snd
    (hφ's : Function.Surjective φ') (hg's : Function.Surjective g') (hg''s : Function.Surjective g'')
    (hw' : ∀ b, a₀ (φ' b) = g' (a' b))
    (hker' : RingHom.ker g' ≤ (RingHom.ker φ').map a')
    (ha' : (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ''))
    (ha'' : (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'')) :
    IsPushout (CommRingCat.ofHom (pullbackSnd φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a'')
      (CommRingCat.ofHom (pullbackSnd g' g'')) := by
  classical
  have ha'x : ∀ x, pullbackFst g' g'' (a x) = a' (pullbackFst φ' φ'' x) := fun x => RingHom.congr_fun ha' x
  have ha''x : ∀ x, pullbackSnd g' g'' (a x) = a'' (pullbackSnd φ' φ'' x) := fun x => RingHom.congr_fun ha'' x
  have hcond : CommRingCat.ofHom (pullbackSnd φ' φ'') ≫ CommRingCat.ofHom a'' =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (pullbackSnd g' g'') := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha'']

  have hsA : Function.Surjective (pullbackSnd g' g'') := fun x'' => by
    obtain ⟨x', hx'⟩ := hg's (g'' x'')
    exact ⟨⟨(x', x''), show g' x' = g'' x'' from hx'⟩, rfl⟩

  have hkill : ∀ (T : Type) [CommRing T] (u : B'' →+* T) (v : pullbackRing g' g'' →+* T),
      (∀ x, u (pullbackSnd φ' φ'' x) = v (a x)) →
      ∀ z : pullbackRing g' g'', pullbackSnd g' g'' z = 0 → v z = 0 := by
    intro T _ u v huv z hz
    have hz2 : z.1.2 = 0 := hz
    have hy : z.1.1 ∈ RingHom.ker g' := by
      rw [RingHom.mem_ker]
      have hz1 : g' z.1.1 = g'' z.1.2 := z.2
      rw [hz1, hz2, map_zero]
    have hyJ := hker' hy
    have main : ∀ y ∈ (RingHom.ker φ').map a',
        ∃ hm : (y, (0 : A'')) ∈ pullbackRing g' g'', v ⟨(y, (0 : A'')), hm⟩ = 0 := by
      intro y hy'
      rw [Ideal.map] at hy'
      induction hy' using Submodule.span_induction with
      | mem y hy0 =>
          obtain ⟨k, hk, rfl⟩ := hy0
          have hk0 : φ' k = 0 := hk
          have hm : (a' k, (0 : A'')) ∈ pullbackRing g' g'' := by
            show g' (a' k) = g'' 0
            rw [map_zero, ← hw', hk0, map_zero]
          refine ⟨hm, ?_⟩
          let pk : pullbackRing φ' φ'' := ⟨(k, (0 : B'')), show φ' k = φ'' 0 by rw [map_zero, hk0]⟩
          have hapk : a pk = ⟨(a' k, (0 : A'')), hm⟩ := by
            apply Subtype.ext
            apply Prod.ext
            · show pullbackFst g' g'' (a pk) = a' k
              rw [ha'x]; rfl
            · show pullbackSnd g' g'' (a pk) = 0
              rw [ha''x]; show a'' 0 = 0; exact map_zero a''
          rw [← hapk, ← huv]
          show u 0 = 0
          exact map_zero u
      | zero =>
          refine ⟨show g' 0 = g'' 0 by rw [map_zero, map_zero], ?_⟩
          have : (⟨((0 : A'), (0 : A'')), show g' 0 = g'' 0 by rw [map_zero, map_zero]⟩ : pullbackRing g' g'') = 0 := rfl
          rw [this, map_zero]
      | add y₁ y₂ _ _ h₁ h₂ =>
          obtain ⟨hm₁, hv₁⟩ := h₁
          obtain ⟨hm₂, hv₂⟩ := h₂
          have hm : (y₁ + y₂, (0 : A'')) ∈ pullbackRing g' g'' := by
            have := (pullbackRing g' g'').add_mem hm₁ hm₂
            simpa using this
          refine ⟨hm, ?_⟩
          have : (⟨(y₁ + y₂, (0 : A'')), hm⟩ : pullbackRing g' g'') = ⟨(y₁, (0 : A'')), hm₁⟩ + ⟨(y₂, (0 : A'')), hm₂⟩ := by
            apply Subtype.ext; apply Prod.ext
            · rfl
            · show (0 : A'') = 0 + 0; rw [add_zero]
          rw [this, map_add, hv₁, hv₂, add_zero]
      | smul r y _ h =>
          obtain ⟨hm, hv⟩ := h
          obtain ⟨r'', hr''⟩ := hg''s (g' r)
          have hL : (r, r'') ∈ pullbackRing g' g'' := show g' r = g'' r'' from hr''.symm
          have hm' : (r • y, (0 : A'')) ∈ pullbackRing g' g'' := by
            have := (pullbackRing g' g'').mul_mem hL hm
            simpa [smul_eq_mul] using this
          refine ⟨hm', ?_⟩
          have : (⟨(r • y, (0 : A'')), hm'⟩ : pullbackRing g' g'') = ⟨(r, r''), hL⟩ * ⟨(y, (0 : A'')), hm⟩ := by
            apply Subtype.ext; apply Prod.ext
            · show r • y = r * y; rfl
            · show (0 : A'') = r'' * 0; rw [mul_zero]
          rw [this, map_mul, hv, mul_zero]
    obtain ⟨hm, hv⟩ := main z.1.1 hyJ
    have hz' : z = ⟨(z.1.1, (0 : A'')), hm⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · exact hz2
    rw [hz']
    exact hv

  have key : ∀ (T : Type) [CommRing T] (u : B'' →+* T) (v : pullbackRing g' g'' →+* T),
      (∀ x, u (pullbackSnd φ' φ'' x) = v (a x)) →
      ∃ w : A'' →+* T, (∀ z, w (pullbackSnd g' g'' z) = v z) ∧ (∀ b, w (a'' b) = u b) := by
    intro T _ u v huv
    have hv : ∀ z ∈ RingHom.ker (pullbackSnd g' g''), v z = 0 := fun z hz => hkill T u v huv z hz
    let e : (pullbackRing g' g'' ⧸ RingHom.ker (pullbackSnd g' g'')) ≃+* A'' :=
      RingEquiv.ofBijective (RingHom.kerLift (pullbackSnd g' g''))
        ⟨RingHom.kerLift_injective _, fun x'' => by
          obtain ⟨z, rfl⟩ := hsA x''
          exact ⟨Ideal.Quotient.mk _ z, RingHom.kerLift_mk _ z⟩⟩
    have he : ∀ z, e.symm (pullbackSnd g' g'' z) = Ideal.Quotient.mk _ z := fun z => by
      apply e.injective; rw [e.apply_symm_apply]; exact (RingHom.kerLift_mk _ z).symm
    let l : (pullbackRing g' g'' ⧸ RingHom.ker (pullbackSnd g' g'')) →+* T :=
      Ideal.Quotient.lift _ v hv
    refine ⟨l.comp e.symm.toRingHom, fun z => ?_, fun b => ?_⟩
    · show l (e.symm (pullbackSnd g' g'' z)) = v z
      rw [he]; rfl
    · obtain ⟨b', hb'⟩ := hφ's (φ'' b)
      let pb : pullbackRing φ' φ'' := ⟨(b', b), show φ' b' = φ'' b from hb'⟩
      have h1 : a'' b = pullbackSnd g' g'' (a pb) := by rw [ha''x]; rfl
      show l (e.symm (a'' b)) = u b
      rw [h1, he]
      show v (a pb) = u b
      rw [← huv]; rfl
  refine IsPushout.of_isColimit' ⟨hcond⟩ ?_
  refine PushoutCocone.IsColimit.mk hcond
    (fun s => CommRingCat.ofHom (Classical.choose (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition)))) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext; apply RingHom.ext; intro b
    exact (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).2 b
  · intro s
    apply CommRingCat.hom_ext; apply RingHom.ext; intro z
    exact (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).1 z
  · intro s m hm₁ hm₂
    apply CommRingCat.hom_ext; apply RingHom.ext; intro x''
    obtain ⟨z, rfl⟩ := hsA x''
    have e1 := (Classical.choose_spec (key s.pt s.inl.hom s.inr.hom
      (fun x => congrArg (fun f => CommRingCat.Hom.hom f x) s.condition))).1 z
    have e2 : m.hom (pullbackSnd g' g'' z) = s.inr.hom z := congrArg (fun f => CommRingCat.Hom.hom f z) hm₂
    exact e2.trans e1.symm

end SquaresSnd

end AlphaFlatTriple

open AlphaFlatTriple in
theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
    (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
    (H' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom a') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g'))
    (H'' : IsPushout (CommRingCat.ofHom φ'') (CommRingCat.ofHom a'') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g''))
    (hfl' : a'.Flat) (hfl'' : a''.Flat) :
    ∃ a : pullbackRing φ' φ'' →+* pullbackRing g' g'',
      (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ'') ∧
      (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'') ∧

      IsPullback (CommRingCat.ofHom (pullbackFst g' g'')) (CommRingCat.ofHom (pullbackSnd g' g''))
        (CommRingCat.ofHom g') (CommRingCat.ofHom g'') ∧
      Function.Surjective g'' ∧ (∀ x ∈ RingHom.ker g'', IsNilpotent x) ∧

      IsPushout (CommRingCat.ofHom (pullbackFst φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a')
        (CommRingCat.ofHom (pullbackFst g' g'')) ∧
      IsPushout (CommRingCat.ofHom (pullbackSnd φ' φ'')) (CommRingCat.ofHom a) (CommRingCat.ofHom a'')
        (CommRingCat.ofHom (pullbackSnd g' g'')) ∧

      a.Flat ∧ (a'.FinitePresentation → a''.FinitePresentation → a.FinitePresentation) := by
  have hw' : ∀ b, a₀ (φ' b) = g' (a' b) := fun b => by
    have := congrArg (fun f => CommRingCat.Hom.hom f b) H'.w
    simpa using this
  have hw'' : ∀ b, a₀ (φ'' b) = g'' (a'' b) := fun b => by
    have := congrArg (fun f => CommRingCat.Hom.hom f b) H''.w
    simpa using this
  have hcomp : g'.comp (a'.comp (pullbackFst φ' φ'')) = g''.comp (a''.comp (pullbackSnd φ' φ'')) := by
    apply RingHom.ext
    intro x
    have hx : φ' x.1.1 = φ'' x.1.2 := x.2
    show g' (a' x.1.1) = g'' (a'' x.1.2)
    rw [← hw', hx, hw'']
  have hg's := surjective_of_isPushout φ' a' a₀ g' H' hφ's
  have hg''s := surjective_of_isPushout φ'' a'' a₀ g'' H'' hφ''s
  have hker' := ker_le_map_of_isPushout φ' a' a₀ g' H' hφ's
  have hker'' := ker_le_map_of_isPushout φ'' a'' a₀ g'' H'' hφ''s
  have hc1 := pullbackFst_comp_pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp
  have hc2 := pullbackSnd_comp_pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp
  have hflat : a'.Flat → a''.Flat →
      (pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp).Flat :=
    fun h1 h2 => RingHom.Flat.of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent φ' φ'' hφ's hφ''s hφ'n hφ''n
      a' a'' a₀ g' g'' H' H'' h1 h2 _ hc1 hc2
  refine ⟨pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp,
    hc1, hc2, ?_, hg''s, ?_, ?_, ?_, hflat hfl' hfl'', ?_⟩
  · exact IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom g') (CommRingCat.ofHom g''))
  · intro x hx
    obtain ⟨n, hn⟩ := hφ''n
    refine ⟨n, ?_⟩
    have h1 : x ^ n ∈ ((RingHom.ker φ'').map a'') ^ n := Ideal.pow_mem_pow (hker'' hx) n
    rw [← Ideal.map_pow, hn] at h1
    simpa using h1
  · exact isPushout_fst φ' φ'' a' a'' a₀ g' g'' _ hφ''s hg's hg''s hw'' hker'' hc1 hc2
  · exact isPushout_snd φ' φ'' a' a'' a₀ g' g'' _ hφ's hg's hg''s hw' hker' hc1 hc2
  ·
    intro hfp' hfp''
    letI algA : Algebra (pullbackRing φ' φ'') (pullbackRing g' g'') :=
      (pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp).toAlgebra
    letI algA' : Algebra B' A' := a'.toAlgebra
    haveI hflatI : Module.Flat (pullbackRing φ' φ'') (pullbackRing g' g'') := hflat hfl' hfl''
    have haS : ∀ x, (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'')) x =
        pullbackStr g' g'' (a'.comp (pullbackFst φ' φ'')) (a''.comp (pullbackSnd φ' φ'')) hcomp x := fun x => rfl

    have hp : Function.Surjective (pullbackFst φ' φ'') := fun b => by
      obtain ⟨b'', h⟩ := hφ''s (φ' b)
      exact ⟨⟨(b, b''), show φ' b = φ'' b'' from h.symm⟩, rfl⟩
    have hle : RingHom.ker (pullbackFst φ' φ'') ≤ (RingHom.ker φ'').comap (pullbackSnd φ' φ'') := by
      intro x hx
      have hx1 : x.1.1 = 0 := hx
      have hx2 : φ' x.1.1 = φ'' x.1.2 := x.2
      show φ'' x.1.2 = 0
      rw [← hx2, hx1, map_zero]
    have hI : IsNilpotent (RingHom.ker (pullbackFst φ' φ'')) := by
      obtain ⟨n, hn⟩ := hφ''n
      replace hn : RingHom.ker φ'' ^ n = ⊥ := hn
      refine ⟨n + 1, ?_⟩
      show RingHom.ker (pullbackFst φ' φ'') ^ (n + 1) = ⊥
      rw [← le_bot_iff]
      intro x hx
      have h1 : x ∈ RingHom.ker (pullbackFst φ' φ'') := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
      have h2 := Ideal.le_comap_pow _ (n + 1) (Ideal.pow_right_mono hle (n + 1) hx)
      have hK : RingHom.ker φ'' ^ (n + 1) = ⊥ := by
        rw [← le_bot_iff, ← hn]; exact Ideal.pow_le_pow_right (Nat.le_succ n)
      rw [hK] at h2
      have h2' : x.1.2 = 0 := h2
      have h1' : x.1.1 = 0 := h1
      rw [Ideal.mem_bot]
      exact Subtype.ext (Prod.ext h1' h2')

    have hq : Function.Surjective (pullbackFst g' g'') := fun x' => by
      obtain ⟨x'', hx''⟩ := hg''s (g' x')
      exact ⟨⟨(x', x''), show g' x' = g'' x'' from hx''.symm⟩, rfl⟩
    have hc1x : ∀ x, pullbackFst g' g'' (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'') x) =
        a' (pullbackFst φ' φ'' x) := fun x => by rw [haS]; exact RingHom.congr_fun hc1 x
    have hkerq : RingHom.ker (pullbackFst g' g'') =
        (RingHom.ker (pullbackFst φ' φ'')).map (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'')) := by
      apply le_antisymm
      · intro z hz
        have hz1 : z.1.1 = 0 := hz
        have hy : z.1.2 ∈ RingHom.ker g'' := by
          rw [RingHom.mem_ker]
          have hz2 : g' z.1.1 = g'' z.1.2 := z.2
          rw [← hz2, hz1, map_zero]
        have hyJ := hker'' hy
        have main : ∀ y ∈ (RingHom.ker φ'').map a'',
            ∃ hm : ((0 : A'), y) ∈ pullbackRing g' g'',
              (⟨((0 : A'), y), hm⟩ : pullbackRing g' g'') ∈
                (RingHom.ker (pullbackFst φ' φ'')).map (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'')) := by
          intro y hy'
          rw [Ideal.map] at hy'
          induction hy' using Submodule.span_induction with
          | mem y hy0 =>
              obtain ⟨k, hk, rfl⟩ := hy0
              have hk0 : φ'' k = 0 := hk
              have hm : ((0 : A'), a'' k) ∈ pullbackRing g' g'' := by
                show g' 0 = g'' (a'' k)
                rw [map_zero, ← hw'', hk0, map_zero]
              refine ⟨hm, ?_⟩
              let pk : pullbackRing φ' φ'' := ⟨((0 : B'), k), show φ' 0 = φ'' k by rw [map_zero, hk0]⟩
              have hpk : pk ∈ RingHom.ker (pullbackFst φ' φ'') := rfl
              have hapk : algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'') pk = ⟨((0 : A'), a'' k), hm⟩ := by
                rw [haS]
                apply Subtype.ext; apply Prod.ext
                · show a' 0 = 0; exact map_zero a'
                · rfl
              rw [← hapk]
              exact Ideal.mem_map_of_mem _ hpk
          | zero =>
              refine ⟨show g' 0 = g'' 0 by rw [map_zero, map_zero], ?_⟩
              have : (⟨((0 : A'), (0 : A'')), show g' 0 = g'' 0 by rw [map_zero, map_zero]⟩ : pullbackRing g' g'') = 0 := rfl
              rw [this]; exact Submodule.zero_mem _
          | add y₁ y₂ _ _ h₁ h₂ =>
              obtain ⟨hm₁, hv₁⟩ := h₁
              obtain ⟨hm₂, hv₂⟩ := h₂
              have hm : ((0 : A'), y₁ + y₂) ∈ pullbackRing g' g'' := by
                have := (pullbackRing g' g'').add_mem hm₁ hm₂
                simpa using this
              refine ⟨hm, ?_⟩
              have : (⟨((0 : A'), y₁ + y₂), hm⟩ : pullbackRing g' g'') = ⟨((0 : A'), y₁), hm₁⟩ + ⟨((0 : A'), y₂), hm₂⟩ := by
                apply Subtype.ext; apply Prod.ext
                · show (0 : A') = 0 + 0; rw [add_zero]
                · rfl
              rw [this]; exact Ideal.add_mem _ hv₁ hv₂
          | smul r y _ h =>
              obtain ⟨hm, hv⟩ := h
              obtain ⟨r', hr'⟩ := hg's (g'' r)
              have hL : (r', r) ∈ pullbackRing g' g'' := show g' r' = g'' r from hr'
              have hm' : ((0 : A'), r • y) ∈ pullbackRing g' g'' := by
                have := (pullbackRing g' g'').mul_mem hL hm
                simpa [smul_eq_mul] using this
              refine ⟨hm', ?_⟩
              have : (⟨((0 : A'), r • y), hm'⟩ : pullbackRing g' g'') = ⟨(r', r), hL⟩ * ⟨((0 : A'), y), hm⟩ := by
                apply Subtype.ext; apply Prod.ext
                · show (0 : A') = r' * 0; rw [mul_zero]
                · show r • y = r * y; rfl
              rw [this]; exact Ideal.mul_mem_left _ _ hv
        obtain ⟨hm, hv⟩ := main z.1.2 hyJ
        have hz' : z = ⟨((0 : A'), z.1.2), hm⟩ := by
          apply Subtype.ext; apply Prod.ext
          · exact hz1
          · rfl
        rw [hz']
        exact hv
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        have hx0 : pullbackFst φ' φ'' x = 0 := hx
        show pullbackFst g' g'' (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'') x) = 0
        rw [hc1x, hx0, map_zero]
    have hcommq : (pullbackFst g' g'').comp (algebraMap (pullbackRing φ' φ'') (pullbackRing g' g'')) =
        (algebraMap B' A').comp (pullbackFst φ' φ'') := by
      apply RingHom.ext; intro x; exact hc1x x
    have hfpA' : Algebra.FinitePresentation B' A' := hfp'
    exact Algebra.FinitePresentation.of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
      (pullbackFst φ' φ'') hp hI (pullbackFst g' g'') hq hcommq hkerq hfpA'

end S_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent (solution)
