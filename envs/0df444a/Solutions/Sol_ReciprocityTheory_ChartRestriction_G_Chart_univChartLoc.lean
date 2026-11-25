-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:36.179336+00:00
-- url     : https://prove2.me/submissions/1c308620-d307-49da-8613-54b0246af3f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_algChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
private lemma mem_of_local_lemma [IsLocalRing R] {X : Scheme} (e : Spec (CommRingCat.of R) ⟶ X)
    (U : X.Opens) (hU : e.base (IsLocalRing.closedPoint R) ∈ U) (w : Spec (CommRingCat.of R)) :
    e.base w ∈ U := by
  have hs : (w : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R :=
    IsLocalRing.specializes_closedPoint _
  first
  | exact (hs.map e.base.hom.continuous).mem_open U.isOpen hU
  | exact (hs.map e.continuous).mem_open U.isOpen hU
  | exact (hs.map e.base.continuous).mem_open U.isOpen hU
private lemma surj_lemma_2 {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ)
    (hm : (RingHom.ker aug) ^ (m + 1) = ⊥) (z : Spec (CommRingCat.of A)) :
    ∃ w : Spec (CommRingCat.of R), (Spec.map (CommRingCat.ofHom aug.toRingHom)).base w = z := by
  have hsurj : Function.Surjective aug := fun r => ⟨algebraMap R A r, by simp⟩
  have hsurj' : Function.Surjective aug.toRingHom := hsurj
  let P : Ideal A := (z : PrimeSpectrum A).asIdeal
  haveI hP : P.IsPrime := (z : PrimeSpectrum A).isPrime
  have hker : RingHom.ker aug ≤ P := fun x hx => by
    have h1 : x ^ (m + 1) ∈ (RingHom.ker aug) ^ (m + 1) := Ideal.pow_mem_pow hx _
    rw [hm, Ideal.mem_bot] at h1
    exact hP.mem_of_pow_mem (m + 1) (by rw [h1]; exact P.zero_mem)
  haveI hQ : (Ideal.map aug P).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  refine ⟨(PrimeSpectrum.mk (Ideal.map aug P) hQ : PrimeSpectrum R), ?_⟩
  apply PrimeSpectrum.ext
  first
  | (change Ideal.comap aug (Ideal.map aug P) = P
     rw [Ideal.comap_map_of_surjective _ hsurj]
     exact sup_eq_left.mpr hker)
  | (change Ideal.comap aug.toRingHom (Ideal.map aug.toRingHom P) = P
     rw [Ideal.comap_map_of_surjective _ hsurj']
     exact sup_eq_left.mpr hker)
private lemma spMap_inj_lemma_3 {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    {g g' : B →ₐ[R] A} (h : spMap (R₀ := R) g = spMap g') : g = g' := by
  have h1 : Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom g'.toRingHom) := congrArg (fun k => k.left) h
  have h2 := Spec.map_inj.mp h1
  ext b
  have h3 := congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of A => k.hom b) h2
  simpa using h3
private lemma exists_spMap_lemma_4 {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (h : sp (R₀ := R) A ⟶ sp B) : ∃ φ : B →ₐ[R] A, h = spMap φ := by
  let f : CommRingCat.of B ⟶ CommRingCat.of A :=
    Spec.preimage (h.left : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
  have hf : Spec.map f = h.left := Spec.map_preimage _
  have hw : Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [hf]; exact Over.w h
  rw [← Spec.map_comp] at hw
  have hw' := Spec.map_inj.mp hw
  have hc : ∀ r : R, f.hom (algebraMap R B r) = algebraMap R A r := fun r => by
    have h3 := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of A => k.hom r) hw'
    simpa using h3
  refine ⟨{ f.hom with commutes' := hc }, ?_⟩
  apply Over.OverMorphism.ext
  rw [spMap_left, ← hf]
  rfl
private lemma one_left_lemma_5 (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (X : Over (Spec (CommRingCat.of R))) :
    (1 : X ⟶ G).left = X.hom ≫ (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left := by
  have h1 : (1 : X ⟶ G) = toUnit X ≫ MonObj.one := by
    first | rfl | exact Hom.one_def | simp [Hom.one_def]
  have h2 : (toUnit X).left ≫ 𝟙 (Spec (CommRingCat.of R)) = X.hom := Over.w (toUnit X)
  have h2' : (toUnit X).left = X.hom := by
    refine Eq.trans ?_ h2
    exact (Category.comp_id _).symm
  rw [h1, Over.comp_left, h2']
private lemma comp_one_lemma_6 (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) : f ≫ (1 : Y ⟶ G) = 1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, one_left_lemma_5, one_left_lemma_5, ← Category.assoc, Over.w f]
private lemma cancel_lemma_7 {A : Type} [CommRing A] [Algebra R A] {X : Over (Spec (CommRingCat.of R))}
    {P : Type} [CommRing P] [Algebra R P] (jU : sp (R₀ := R) P ⟶ X) [Mono jU.left]
    {g g' : P →ₐ[R] A} (h : spMap (R₀ := R) g ≫ jU = spMap g' ≫ jU) : g = g' := by
  apply spMap_inj_lemma_3
  apply Over.OverMorphism.ext
  have h1 := congrArg (fun k => k.left) h
  simp only [Over.comp_left] at h1
  exact (cancel_mono jU.left).mp h1
end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] :
    ∃ (d : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x := by
  classical
  let e : Spec (CommRingCat.of R) ⟶ G.left :=
    (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left
  have he : e ≫ G.hom = 𝟙 (Spec (CommRingCat.of R)) :=
    Over.w (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)

  obtain ⟨U, hU, hqU⟩ : ∃ U : G.left.Opens, IsAffineOpen U ∧
      e.base (IsLocalRing.closedPoint R) ∈ U := by
    first
    | (obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
          (show e.base (IsLocalRing.closedPoint R) ∈ (⊤ : G.left.Opens) from trivial)
       exact ⟨W, hW, hxW⟩)
    | (obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
          G.left.isBasis_affineOpens)
          (show e.base (IsLocalRing.closedPoint R) ∈ (⊤ : G.left.Opens) from trivial)
       exact ⟨W, hW, hxW⟩)
    | (obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
          (isBasis_affineOpens G.left))
          (show e.base (IsLocalRing.closedPoint R) ∈ (⊤ : G.left.Opens) from trivial)
       exact ⟨W, hW, hxW⟩)
  have he_mem : ∀ w, e.base w ∈ U := mem_of_local_lemma e U hqU
  let jU := hU.fromSpec
  haveI hjUo : IsOpenImmersion jU := (inferInstance : IsOpenImmersion hU.fromSpec)
  have hrange : Set.range jU.base = (U : Set G.left) := hU.range_fromSpec
  let Bc : CommRingCat := G.left.presheaf.obj (Opposite.op U)
  let fB : CommRingCat.of R ⟶ Bc :=
    Spec.preimage (jU ≫ G.hom : Spec Bc ⟶ Spec (CommRingCat.of R))
  have hfB : Spec.map fB = jU ≫ G.hom := Spec.map_preimage _
  letI : Algebra R Bc := fB.hom.toAlgebra
  let jO : sp (R₀ := R) Bc ⟶ G := Over.homMk jU hfB.symm
  haveI hmono : Mono jO.left := (inferInstance : Mono jU)

  have hsm : Smooth (jU ≫ G.hom) := by
    first
    | exact inferInstance
    | (haveI : Smooth jU := inferInstance; exact inferInstance)
    | (haveI : Etale jU := inferInstance; haveI : Smooth jU := inferInstance; exact inferInstance)
  haveI hBsm : Algebra.Smooth R Bc := by
    have h2 : Smooth (Spec.map fB) := by rw [hfB]; exact hsm
    first
    | exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h2
    | exact (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := @RingHom.Smooth)).mp h2

  have hsub : Set.range e.base ⊆ Set.range jU.base := by
    rw [hrange]; rintro _ ⟨w, rfl⟩; exact he_mem w
  let e' : Spec (CommRingCat.of R) ⟶ Spec Bc := IsOpenImmersion.lift jU e hsub
  have he' : e' ≫ jU = e := IsOpenImmersion.lift_fac _ _ _
  let eps0 : Bc ⟶ CommRingCat.of R := Spec.preimage e'
  have hε : Spec.map eps0 = e' := Spec.map_preimage _
  have heps0 : fB ≫ eps0 = 𝟙 _ := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, Spec.map_id, hε, hfB, ← Category.assoc, he', he]
  have hc : ∀ r : R, eps0.hom (algebraMap R Bc r) = algebraMap R R r := fun r => by
    have h3 := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k.hom r) heps0
    change eps0.hom (fB.hom r) = r
    simpa using h3
  let eps : Bc →ₐ[R] R := { eps0.hom with commutes' := hc }
  have h1 : spMap (R₀ := R) eps ≫ jO = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left_lemma_5]
    change Spec.map eps0 ≫ jU = Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ e
    rw [hε, he']
    first
    | rw [Algebra.id.map_eq_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    | simp

  obtain ⟨n, pr, hpr1, hpr2, hpr3⟩ := algChart Bc eps
  refine ⟨n, fun m => spMap (pr m) ≫ jO, ?_⟩
  unfold IsUnivChart
  refine ⟨?_, ?_, ?_⟩
  · intro m
    try dsimp only
    rw [← Category.assoc, spMap_comp, hpr1]
  · intro m
    try dsimp only
    rw [← Category.assoc, spMap_comp, hpr2, ← spMap_comp, Category.assoc, h1, comp_one_lemma_6]
  · intro A _ _ aug m hm y hy
    have hyl : (spMap (R₀ := R) aug).left ≫ y.left = e := by
      have h0 := congrArg (fun k => k.left) hy
      simp only [Over.comp_left, one_left_lemma_5] at h0
      rw [h0]
      change Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ e = e
      first
      | rw [Algebra.id.map_eq_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      | simp

    have hyU : Set.range y.left.base ⊆ Set.range jU.base := by
      rw [hrange]
      rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := surj_lemma_2 aug m hm z
      have key : y.left.base ((Spec.map (CommRingCat.ofHom aug.toRingHom)).base w) =
          e.base w := by
        rw [← hyl]
        first | rfl | simp
      rw [key]
      exact he_mem w
    let y' : Spec (CommRingCat.of A) ⟶ Spec Bc := IsOpenImmersion.lift jU y.left hyU
    have hy' : y' ≫ jU = y.left := IsOpenImmersion.lift_fac _ _ _
    let yO : sp (R₀ := R) A ⟶ sp (R₀ := R) Bc := Over.homMk y' (by
      change y' ≫ Spec.map fB = _
      rw [hfB, ← Category.assoc, hy']
      exact Over.w y)
    have hyO : yO ≫ jO = y := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left]
      exact hy'
    obtain ⟨φ, hφ⟩ := exists_spMap_lemma_4 yO
    have haug : aug.comp φ = eps := by
      apply cancel_lemma_7 jO
      rw [← spMap_comp, Category.assoc, ← hφ, hyO, hy, h1]
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := hpr3 A aug m hm φ haug
    refine ⟨ψ, ⟨hψ1, ?_⟩, ?_⟩
    · try dsimp only
      rw [← hyO, hφ, ← Category.assoc, spMap_comp, hψ2]
    · rintro ψ' ⟨hψ'1, hψ'2⟩
      apply hψu ψ'
      refine ⟨hψ'1, ?_⟩
      apply cancel_lemma_7 jO
      rw [← spMap_comp, Category.assoc, ← hφ, hyO]
      exact hψ'2.symm
end ReciprocityTheory.ChartRestriction.G.Chart
