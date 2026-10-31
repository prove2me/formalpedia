-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P03.cech_cohomologous_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:36:28.500953+00:00
-- url     : https://prove2.me/submissions/ecfbe7c1-5cfa-4585-a09f-5dcdf5feda2d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P03

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P03
universe u

private theorem open_compactlyGenerated {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] {V : Set X} (hV : IsOpen V) :
    CompactlyGeneratedSpace V := by
  apply compactlyGeneratedSpace_of_isOpen
  intro A hA
  rw [hV.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
  apply CompactlyGeneratedSpace.isOpen'
  intro K _ _ _ g hg
  let W : Set K := g ⁻¹' V
  have hW : IsOpen W := hV.preimage hg
  letI : LocallyCompactSpace W := hW.locallyCompactSpace
  let l : W → V := fun x => ⟨g x, x.property⟩
  have hl : Continuous l := (hg.comp continuous_subtype_val).subtype_mk _
  have ho : IsOpen (l ⁻¹' A) := by
    apply CompactlyGeneratedSpace.isOpen'
    intro S _ _ _ q hq
    exact hA S (l ∘ q) (hl.comp hq)
  have hi := hW.isOpenEmbedding_subtypeVal.isOpenMap _ ho
  convert hi using 1
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    refine ⟨⟨x, ?_⟩, ?_, rfl⟩
    · show g x ∈ V
      rw [← he]
      exact y.property
    · change l _ ∈ A
      convert hy using 1
      exact Subtype.ext he.symm
  · rintro ⟨y, hy, he⟩
    exact ⟨l y, hy, congrArg g he⟩

private theorem binary_continuous {X Y Z S : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace S] [CompactlyGeneratedSpace S]
    {f : X → Y → Z} (hf : KContinuousTwo f)
    (a : C(S, X)) (b : C(S, Y)) : Continuous (fun s => f (a s) (b s)) := by
  apply continuous_from_compactlyGeneratedSpace
  intro K _ _ _ g hg
  exact hf (CompHaus.of K) ⟨a ∘ g, a.continuous.comp hg⟩
    ⟨b ∘ g, b.continuous.comp hg⟩

section Algebra
variable {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
variable (C : TopologicalCrossedModule G H)

private theorem action_inverse_cancel (g : G) (z : H) :
    C.rho g (C.rho g⁻¹ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel]
  simp

private theorem action_slide (fi fj g g' : G) (k z : H)
    (h : C.boundary k * g * fj = fi * g') :
    C.rho fi (C.rho g' z) * k = k * C.rho g (C.rho fj z) := by
  have he := congrArg (fun q => C.rho q z) h
  simp only [map_mul, MulAut.mul_apply, C.peiffer] at he
  rw [← he]
  group

private theorem compose_square (fi fj fi' fj' g g' g'' : G) (k k' : H)
    (h : C.boundary k * g * fj = fi * g')
    (h' : C.boundary k' * g' * fj' = fi' * g'') :
    C.boundary (C.rho fi k' * k) * g * (fj * fj') = (fi * fi') * g'' := by
  rw [map_mul, C.equivariance]
  calc
    (fi * C.boundary k' * fi⁻¹ * C.boundary k) * g * (fj * fj') =
        fi * C.boundary k' * fi⁻¹ * (C.boundary k * g * fj) * fj' := by group
    _ = fi * (C.boundary k' * g' * fj') := by rw [h]; group
    _ = (fi * fi') * g'' := by rw [h']; group

private theorem compose_prism (fi fj g g' : G)
    (kil kij kjl kil' kij' kjl' ha hb hc : H)
    (hs : C.boundary kij * g * fj = fi * g')
    (hp : kil * ha = C.rho fi hb * kij * C.rho g kjl)
    (hp' : kil' * hb = hc * kij' * C.rho g' kjl') :
    (C.rho fi kil' * kil) * ha =
      C.rho fi hc * (C.rho fi kij' * kij) * C.rho g (C.rho fj kjl' * kjl) := by
  calc
    (C.rho fi kil' * kil) * ha = C.rho fi kil' * (kil * ha) := by group
    _ = C.rho fi (kil' * hb) * kij * C.rho g kjl := by rw [hp, map_mul]; group
    _ = C.rho fi hc * C.rho fi kij' * (C.rho fi (C.rho g' kjl') * kij) *
        C.rho g kjl := by rw [hp']; simp only [map_mul]; group
    _ = C.rho fi hc * (C.rho fi kij' * kij) * C.rho g (C.rho fj kjl' * kjl) := by
      rw [action_slide C fi fj g g' kij kjl' hs, map_mul]
      group

private theorem inverse_square (fi fj g g' : G) (k : H)
    (h : C.boundary k * g * fj = fi * g') :
    C.boundary (C.rho fi⁻¹ k⁻¹) * g' * fj⁻¹ = fi⁻¹ * g := by
  rw [C.equivariance, map_inv, inv_inv]
  calc
    (fi⁻¹ * (C.boundary k)⁻¹ * fi) * g' * fj⁻¹ =
        fi⁻¹ * (C.boundary k)⁻¹ * (fi * g') * fj⁻¹ := by group
    _ = fi⁻¹ * g := by rw [← h]; group

private theorem inverse_prism (fi fj g g' : G) (kil kij kjl ha hb : H)
    (hs : C.boundary kij * g * fj = fi * g')
    (hp : kil * ha = C.rho fi hb * kij * C.rho g kjl) :
    C.rho fi⁻¹ kil⁻¹ * hb =
      C.rho fi⁻¹ ha * C.rho fi⁻¹ kij⁻¹ * C.rho g' (C.rho fj⁻¹ kjl⁻¹) := by
  have hslide := action_slide C fi fj g g' kij (C.rho fj⁻¹ kjl⁻¹) hs
  rw [action_inverse_cancel] at hslide
  have hc : C.rho fi (C.rho g' (C.rho fj⁻¹ kjl⁻¹)) =
      kij * C.rho g kjl⁻¹ * kij⁻¹ := by
    rw [← hslide]
    group
  apply (C.rho fi).injective
  simp only [map_mul, action_inverse_cancel]
  rw [hc, map_inv]
  calc
    kil⁻¹ * C.rho fi hb =
        kil⁻¹ * (C.rho fi hb * kij * C.rho g kjl) * (C.rho g kjl)⁻¹ * kij⁻¹ := by group
    _ = ha * kij⁻¹ * (kij * (C.rho g kjl)⁻¹ * kij⁻¹) := by rw [← hp]; group

end Algebra

section Transformations
variable {M I G H : Type u}
variable [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H] [Group G] [Group H]
variable {C : TopologicalCrossedModule G H} {U : OpenCover M I}
variable {a b c : CechCocycle C U}

private def restrictedF (t : CechTransformation a b) (i j : I) :
    C(overlapTwo U i j, G) :=
  ⟨fun x => t.f i ⟨x.val, x.property.1⟩,
    (t.f i).continuous.comp (continuous_subtype_val.subtype_mk _)⟩

private def inverseTransformation (hM : IsKSpace M) (t : CechTransformation a b) :
    CechTransformation b a := by
  letI : CompactlyGeneratedSpace M := hM.1
  refine {
    f := fun i => ⟨fun x => (t.f i x)⁻¹,
      C.objectGroup.2.2.comp (t.f i).continuous⟩
    k := fun i j => ⟨fun x => C.rho (t.f i ⟨x.val, x.property.1⟩)⁻¹ (t.k i j x)⁻¹, ?_⟩
    square := ?_
    prism := ?_
    unit := ?_ }
  · rename_i i j
    letI : CompactlyGeneratedSpace (overlapTwo U i j) :=
      open_compactlyGenerated ((U.isOpen i).inter (U.isOpen j))
    exact binary_continuous C.actionContinuous
      ⟨fun x => (restrictedF t i j x)⁻¹,
        C.objectGroup.2.2.comp (restrictedF t i j).continuous⟩
      ⟨fun x => (t.k i j x)⁻¹, C.arrowKernelGroup.2.2.comp (t.k i j).continuous⟩
  · intro i j x hi hj
    exact inverse_square C _ _ _ _ _ (t.square i j x hi hj)
  · intro i j l x hi hj hl
    exact inverse_prism C _ _ _ _ _ _ _ _ _ (t.square i j x hi hj) (t.prism i j l x hi hj hl)
  · intro i x hi
    change C.rho (t.f i ⟨x, hi⟩)⁻¹ (t.k i i ⟨x, hi, hi⟩)⁻¹ = 1
    rw [t.unit i x hi]
    simp

private def composeTransformation (hM : IsKSpace M)
    (t : CechTransformation a b) (s : CechTransformation b c) : CechTransformation a c := by
  letI : CompactlyGeneratedSpace M := hM.1
  refine {
    f := fun i => ⟨fun x => t.f i x * s.f i x, ?_⟩
    k := fun i j => ⟨fun x => C.rho (t.f i ⟨x.val, x.property.1⟩) (s.k i j x) * t.k i j x, ?_⟩
    square := ?_
    prism := ?_
    unit := ?_ }
  · rename_i i
    letI : CompactlyGeneratedSpace (U.opens i) := open_compactlyGenerated (U.isOpen i)
    exact binary_continuous C.objectGroup.2.1 (t.f i) (s.f i)
  · rename_i i j
    letI : CompactlyGeneratedSpace (overlapTwo U i j) :=
      open_compactlyGenerated ((U.isOpen i).inter (U.isOpen j))
    exact binary_continuous C.arrowKernelGroup.2.1
      ⟨fun x => C.rho (restrictedF t i j x) (s.k i j x),
        binary_continuous C.actionContinuous (restrictedF t i j) (s.k i j)⟩ (t.k i j)
  · intro i j x hi hj
    exact compose_square C _ _ _ _ _ _ _ _ _ (t.square i j x hi hj) (s.square i j x hi hj)
  · intro i j l x hi hj hl
    change (_ * _) * _ = C.rho (_ * _) _ * (_ * _) * C.rho _ (_ * _)
    rw [map_mul, MulAut.mul_apply]
    exact compose_prism C _ _ _ _ _ _ _ _ _ _ _ _ _ (t.square i j x hi hj)
      (t.prism i j l x hi hj hl) (s.prism i j l x hi hj hl)
  · intro i x hi
    change C.rho (t.f i ⟨x, hi⟩) (s.k i i ⟨x, hi, hi⟩) * t.k i i ⟨x, hi, hi⟩ = 1
    rw [s.unit i x hi, t.unit i x hi]
    simp

end Transformations

theorem solution {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (hM : IsKSpace M)
    (C : TopologicalCrossedModule G H) (U : OpenCover M I) :
    Equivalence (Cohomologous (C := C) (U := U)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨identityTransformation a⟩
  · intro a b ⟨t⟩
    exact ⟨inverseTransformation hM t⟩
  · intro a b c ⟨t⟩ ⟨s⟩
    exact ⟨composeTransformation hM t s⟩

#print axioms solution
