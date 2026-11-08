-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf_flasque_of_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:20:31.836684+00:00
-- url     : https://prove2.me/submissions/c6f7a2fc-371c-48e3-9fa2-36f657367791

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P16
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
set_option autoImplicit false

section

open Set
set_option backward.isDefEq.respectTransparency false

namespace BorelLocalCompactAux
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def LocallyBorel (f : X → Y) : Prop :=
  ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    @Measurable U Y (borel U) (borel Y) (fun y => f y)

lemma measurable_inter_open {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : @Measurable U Y (borel U) (borel Y) (fun y => f y))
    {t : Set Y} (ht : @MeasurableSet Y (borel Y) t) :
    @MeasurableSet X (borel X) (U ∩ f ⁻¹' t) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  have hh := hU.isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr (hf ht)
  convert hh using 1
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_image]
  constructor
  · rintro ⟨hx,hfx⟩
    exact ⟨⟨x,hx⟩,hfx,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,hy⟩

lemma measurable_of_locallyBorel [CompactSpace X] {f : X → Y} (h : LocallyBorel f) :
    @Measurable X Y (borel X) (borel Y) f := by
  classical
  letI : MeasurableSpace X := borel X
  letI : MeasurableSpace Y := borel Y
  choose U hU hx hm using h
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x,hx x⟩)
  intro t ht
  have he : f ⁻¹' t = ⋃ x ∈ s, U x ∩ f ⁻¹' t := by
    ext x
    constructor
    · intro hxt
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
      exact mem_iUnion₂.mpr ⟨y,hy,hxy,hxt⟩
    · intro hxt
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hxt
      exact hxy.2
  rw [he]
  exact s.measurableSet_biUnion (fun x _ => measurable_inter_open (hU x) (hm x) ht)

end BorelLocalCompactAux
end

section

open Set
set_option backward.isDefEq.respectTransparency false

namespace BorelLocalCompactAux
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma measurable_of_locallyBorel_lindelof [LindelofSpace X] {f : X → Y}
    (h : LocallyBorel f) : @Measurable X Y (borel X) (borel Y) f := by
  classical
  letI : MeasurableSpace X := borel X
  letI : MeasurableSpace Y := borel Y
  choose U hU hx hm using h
  obtain ⟨s,hsc,hs⟩ := isLindelof_univ.elim_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x,hx x⟩)
  intro t ht
  have he : f ⁻¹' t = ⋃ x ∈ s, U x ∩ f ⁻¹' t := by
    ext x
    constructor
    · intro hxt
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
      exact mem_iUnion₂.mpr ⟨y,hy,hxy,hxt⟩
    · intro hxt
      obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp hxt
      exact hxy.2
  rw [he]
  exact MeasurableSet.biUnion hsc (fun x _ => measurable_inter_open (hU x) (hm x) ht)

end BorelLocalCompactAux
end

section

open Set TopologicalSpace CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

namespace GaugeSecondCountableAux
open QAlgorithms.Papers.Independent.Intakenext100.P16
universe u w

lemma section_borel {X : TopCat.{u}} [SecondCountableTopology X]
    {A : Type w} [TopologicalSpace A] {U : Opens X}
    (s : (measurableFunctionSheaf X A).obj.obj (op U)) :
    @Measurable U A (borel U) (borel A) s.val := by
  apply BorelLocalCompactAux.measurable_of_locallyBorel_lindelof
  intro x
  obtain ⟨V,hx,i,hi⟩ := s.property x
  let W : Set U := Subtype.val ⁻¹' (V : Set X)
  refine ⟨W,V.isOpen.preimage continuous_subtype_val,hx,?_⟩
  have hc : Continuous (fun y : W => (⟨y.val.val,y.property⟩ : V)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  change @Measurable V A (borel V) (borel A)
    (fun y => s.val ⟨y.val,i.le y.property⟩) at hi
  exact hi.comp hc.borel_measurable

lemma flasque (X : TopCat.{u}) [SecondCountableTopology X]
    (A : Type w) [TopologicalSpace A] [Nonempty A] :
    TopCat.Sheaf.IsFlasque (measurableFunctionSheaf X A) := by
  constructor
  intro U V i
  apply (CategoryTheory.epi_iff_surjective _).mpr
  intro s
  letI : MeasurableSpace U.unop := borel U.unop
  haveI : BorelSpace U.unop := ⟨rfl⟩
  letI : MeasurableSpace V.unop := borel V.unop
  haveI : BorelSpace V.unop := ⟨rfl⟩
  letI : MeasurableSpace A := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  have hemb := (Opens.isOpenEmbedding_of_le i.unop.le).measurableEmbedding
  obtain ⟨g,hg,he⟩ := hemb.exists_measurable_extend (section_borel s) (fun _ => ‹Nonempty A›)
  refine ⟨⟨g,TopCat.PrelocalPredicate.sheafifyOf hg⟩,?_⟩
  apply Subtype.ext
  exact he

end GaugeSecondCountableAux
end

universe u w
theorem solution (X : TopCat.{u}) [SecondCountableTopology X]
    (A : Type w) [TopologicalSpace A] [Nonempty A] :
    TopCat.Sheaf.IsFlasque
      (QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf X A) :=
  GaugeSecondCountableAux.flasque X A

#print axioms solution
