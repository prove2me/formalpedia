-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf_flasque
-- status  : ACCEPTED   (disprove)
-- author  : @shivm
-- created : 2026-11-07T14:19:46.294847+00:00
-- url     : https://prove2.me/submissions/e9c8717d-1c27-4450-b5b7-45b490f062e3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P16
import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
set_option autoImplicit false

section

open Set Order Cardinal
set_option backward.isDefEq.respectTransparency false

namespace ClubBorelAux
variable {α : Type*} [LinearOrder α] [WellFoundedLT α]
  [TopologicalSpace α] [OrderTopology α]

def Decided (s : Set α) : Prop := ∃ C : Set α, IsClub C ∧ (C ⊆ s ∨ C ⊆ sᶜ)

lemma closed_dirSupClosed {s : Set α} (hs : IsClosed s) : DirSupClosed s := by
  intro t hts ht _ a ha
  exact hs.closure_subset (closure_mono hts (ha.mem_closure ht))

lemma club_tail (a : α) : IsClub (Ici a) :=
  ⟨closed_dirSupClosed isClosed_Ici,fun x => ⟨max a x,le_max_left _ _,le_max_right _ _⟩⟩

lemma decided_closed {s : Set α} (hs : IsClosed s) : Decided s := by
  classical
  by_cases h : IsCofinal s
  · exact ⟨s,⟨closed_dirSupClosed hs,h⟩,Or.inl Subset.rfl⟩
  · obtain ⟨a,ha⟩ := not_isCofinal_iff.mp h
    refine ⟨Ici a,club_tail a,Or.inr ?_⟩
    intro x hx hxs
    exact (ha x hxs).not_ge hx

lemma decided_compl {s : Set α} (h : Decided s) : Decided sᶜ := by
  obtain ⟨C,hC,hs|hs⟩ := h
  · exact ⟨C,hC,Or.inr (by simpa only [compl_compl] using hs)⟩
  · exact ⟨C,hC,Or.inl hs⟩

lemma decided_iUnion (hcof : cof α ≠ ℵ₀) {s : ℕ → Set α}
    (hs : ∀ i, Decided (s i)) : Decided (⋃ i, s i) := by
  classical
  by_cases h : ∃ i C, IsClub C ∧ C ⊆ s i
  · obtain ⟨i,C,hC,hCs⟩ := h
    exact ⟨C,hC,Or.inl (hCs.trans (subset_iUnion s i))⟩
  · have hh : ∀ i, ∃ C, IsClub C ∧ C ⊆ (s i)ᶜ := by
      intro i
      obtain ⟨C,hC,hCs|hCs⟩ := hs i
      · exact False.elim (h ⟨i,C,hC,hCs⟩)
      · exact ⟨C,hC,hCs⟩
    choose C hC hCs using hh
    refine ⟨⋂ i, C i,IsClub.iInter_of_countable hcof hC,Or.inr ?_⟩
    intro x hx hxs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxs
    exact hCs i (mem_iInter.mp hx i) hi

lemma borel_decided (hcof : cof α ≠ ℵ₀) {s : Set α}
    (hs : @MeasurableSet α (borel α) s) : Decided s := by
  letI : MeasurableSpace α := borel α
  haveI : BorelSpace α := ⟨rfl⟩
  apply MeasurableSet.induction_on_open (C := fun s _ => Decided s) _ _ _ s hs
  · intro U hU
    simpa only [compl_compl] using decided_compl (decided_closed hU.isClosed_compl)
  · intro t ht ht'
    exact decided_compl ht'
  · intro f hf hm hd
    exact decided_iUnion hcof hd

lemma exists_nonborel [Nonempty α] [NoMaxOrder α] (hcof : cof α ≠ ℵ₀)
    (g : α → (ℕ → Bool)) (hg : Function.Injective g) :
    ∃ s : Set α, ¬ @MeasurableSet α (borel α) s := by
  classical
  by_contra! h
  have hd (i : ℕ) := borel_decided hcof (h {x | g x i=true})
  choose C hC hs using hd
  have hcap : IsClub (⋂ i, C i) := IsClub.iInter_of_countable hcof hC
  obtain ⟨x,hx⟩ := hcap.nonempty
  obtain ⟨z,hxz⟩ := exists_gt x
  obtain ⟨y,hy,hzy⟩ := hcap.isCofinal z
  have he : x=y := by
    apply hg
    funext i
    rcases hs i with hi|hi
    · exact (hi (mem_iInter.mp hx i)).trans (hi (mem_iInter.mp hy i)).symm
    · have hxi : g x i≠true := hi (mem_iInter.mp hx i)
      have hyi : g y i≠true := hi (mem_iInter.mp hy i)
      cases hxx : g x i <;> cases hyy : g y i <;> simp_all
  exact (hxz.trans_le hzy).ne he

end ClubBorelAux
end

section

open Set Order Cardinal Ordinal
set_option backward.isDefEq.respectTransparency false

namespace OrdinalBorelAux
abbrev CountableOrd := (ℵ₁ : Cardinal.{0}).ord.ToType

instance : TopologicalSpace CountableOrd := Preorder.topology CountableOrd
instance : OrderTopology CountableOrd := ⟨rfl⟩
instance : Nonempty CountableOrd := Cardinal.nonempty_ord_toType (ne_of_gt (aleph_pos 1))
instance : NoMaxOrder CountableOrd := Cardinal.noMaxOrder (aleph0_le_aleph 1)

lemma cof_eq : Order.cof CountableOrd=ℵ₁ := by
  rw [Ordinal.cof_toType,Cardinal.isRegular_aleph_one.cof_ord]

lemma countable_Iic (a : CountableOrd) : (Iic a).Countable := by
  have hi : (Iio a).Countable := (Cardinal.countable_iff_lt_aleph_one _).mpr
    (Cardinal.mk_Iio_toType_ord_lt a)
  have he : Iic a=Iio a ∪ {a} := by ext x;simp [le_iff_lt_or_eq]
  rw [he]
  exact hi.union (countable_singleton a)

lemma exists_nonborel : ∃ s : Set CountableOrd, ¬ @MeasurableSet CountableOrd (borel CountableOrd) s := by
  have hc : #CountableOrd ≤ #(ℕ → Bool) := by
    simpa only [Cardinal.mk_ord_toType,Cardinal.mk_arrow,Cardinal.mk_bool,Cardinal.mk_nat, Cardinal.lift_id,
      Cardinal.two_power_aleph0] using Cardinal.aleph_one_le_continuum
  obtain ⟨g⟩ := (Cardinal.le_def _ _).mp hc
  apply ClubBorelAux.exists_nonborel _ g g.injective
  rw [cof_eq]
  exact ne_of_gt Cardinal.aleph0_lt_aleph_one

end OrdinalBorelAux
end

section

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace OrdinalTailCubeAux
open OrdinalBorelAux

local instance : MeasurableSpace (ZMod 2) := borel (ZMod 2)
local instance : BorelSpace (ZMod 2) := ⟨rfl⟩

abbrev Cube := CountableOrd → ZMod 2

def tail (a : CountableOrd) : Cube := fun b => (Iic b).indicator (fun _ => 1) a

lemma tail_apply (a b : CountableOrd) : tail a b = if a ≤ b then 1 else 0 := by
  classical
  simp [tail,Set.indicator]

lemma tail_continuous : Continuous tail := by
  apply continuous_pi
  intro b
  have hc : IsClopen (Iic b) := ⟨isClosed_Iic,by
    rw [← Order.Iio_succ b]
    exact isOpen_Iio⟩
  exact hc.continuous_indicator continuous_const

lemma tail_injective : Function.Injective tail := by
  intro a b h
  rcases lt_trichotomy a b with hab|hab|hab
  · have hh := congrFun h a
    simp [tail_apply,not_le_of_gt hab] at hh
  · exact hab
  · have hh := congrFun h b
    simp [tail_apply,not_le_of_gt hab] at hh

lemma tail_ne_zero (a : CountableOrd) : tail a ≠ 0 := by
  intro h
  have hh := congrFun h a
  simpa [tail_apply] using hh

def slice (b : CountableOrd) : Set Cube := {x | x b ≠ 0}

lemma slice_open (b : CountableOrd) : IsOpen (slice b) :=
  isClosed_singleton.isOpen_compl.preimage (continuous_apply b)

lemma slice_ne_zero {b : CountableOrd} {x : Cube} (hx : x ∈ slice b) : x ≠ 0 := by
  intro h
  exact hx (congrFun h b)

lemma exists_slice {x : Cube} (hx : x ≠ 0) : ∃ b, x ∈ slice b := by
  by_contra! h
  apply hx
  funext b
  simpa [slice] using h b

lemma support_slice_countable (s : Set CountableOrd) (b : CountableOrd) :
    ((tail '' s) ∩ slice b).Countable := by
  apply ((countable_Iic b).image tail).mono
  rintro x ⟨⟨a,ha,rfl⟩,hx⟩
  refine ⟨a,?_,rfl⟩
  by_contra h
  change ¬ a ≤ b at h
  exact hx (by rw [tail_apply,if_neg h])

def badFunction (s : Set CountableOrd) (x : Cube) : ZMod 2 :=
  (tail '' s).indicator (fun _ => 1) x

lemma badFunction_tail (s : Set CountableOrd) (a : CountableOrd) :
    badFunction s (tail a) = if a ∈ s then 1 else 0 := by
  classical
  simp [badFunction,Set.indicator,tail_injective.mem_set_image]

lemma badFunction_slice_measurable (s : Set CountableOrd) (b : CountableOrd) :
    @Measurable (slice b) (ZMod 2) (borel (slice b)) (borel (ZMod 2))
      (fun x => badFunction s x) := by
  classical
  letI : MeasurableSpace (slice b) := borel (slice b)
  haveI : BorelSpace (slice b) := ⟨rfl⟩
  have hc : {x : slice b | (x : Cube) ∈ tail '' s}.Countable := by
    have hh : ((fun x : slice b => (x : Cube)) ⁻¹' ((tail '' s) ∩ slice b)).Countable :=
      (support_slice_countable s b).preimage Subtype.val_injective
    apply hh.mono
    intro x hx
    change (x : Cube) ∈ tail '' s ∧ (x : Cube) ∈ slice b
    exact ⟨hx,x.property⟩
  exact Measurable.ite hc.measurableSet measurable_const measurable_const

lemma badFunction_nonmeasurable {s : Set CountableOrd}
    (hs : ¬ @MeasurableSet CountableOrd (borel CountableOrd) s) :
    ¬ @Measurable Cube (ZMod 2) (borel Cube) (borel (ZMod 2)) (badFunction s) := by
  classical
  letI : MeasurableSpace CountableOrd := borel CountableOrd
  haveI : BorelSpace CountableOrd := ⟨rfl⟩
  letI : MeasurableSpace Cube := borel Cube
  haveI : BorelSpace Cube := ⟨rfl⟩
  intro hf
  have h := (hf.comp tail_continuous.borel_measurable) (measurableSet_singleton 1)
  apply hs
  convert h using 1
  ext a
  simp [badFunction_tail]

end OrdinalTailCubeAux
end

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

open Set Filter Topology
set_option backward.isDefEq.respectTransparency false

namespace GaugeDiscreteAux
open QAlgorithms.Papers.Independent.Renew46.P29
open QAlgorithms.Papers.Independent.Intakenext100.P16
universe v w

lemma scalarSmooth_subsingleton {D F : Type*}
    [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [Subsingleton F]
    (U : Set D) (f : D → F) : ScalarSmoothOn ℝ U f := by
  dsimp [ScalarSmoothOn]
  constructor
  · refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [_root_.sub_self,smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))
  · refine ⟨fun _ => 0, ?_⟩
    intro x hx h
    have he : f (x + h) = f x := Subsingleton.elim _ _
    have hf : f = fun _ => (0 : F) := funext (fun _ => Subsingleton.elim _ _)
    rw [hf]
    simpa only [_root_.sub_self,smul_zero,LinearMap.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

lemma manifoldSmooth_subsingleton_model {D F X A : Type*}
    [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [Subsingleton F]
    [TopologicalSpace X] [TopologicalSpace A] [ChartedSpace D X] [ChartedSpace F A]
    (U : Set X) (f : X → A) (hf : ContinuousOn f U) :
    ManifoldSmoothOn ℝ (E := D) (F := F) U f := by
  refine ⟨hf,?_⟩
  intro c hc e he
  exact scalarSmooth_subsingleton _ _

def discreteCoefficient (A : Type w) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [ParacompactSpace A]
    [ChartedSpace PUnit.{v+1} A] : FrechetAbelianLieData PUnit.{v+1} A where
  uniform_add := inferInstance
  complete := inferInstance
  metrizable := inferInstance
  lie := by
    letI : ChartedSpace (PUnit.{v+1} × PUnit.{v+1}) (A × A) :=
      prodChartedSpace PUnit.{v+1} A PUnit.{v+1} A
    have hm : LocallyConvexModel ℝ PUnit.{v+1} := by
      refine ⟨inferInstance,inferInstance,inferInstance,
        (inferInstance : Module ℝ PUnit.{v+1}),?_⟩
      exact ⟨inferInstance,inferInstance⟩
    refine ⟨hm,inferInstance,?_,?_,?_⟩
    · constructor
      · intro c hc e he
        exact (scalarSmooth_subsingleton _ _).1
      · intro c hc e he
        exact scalarSmooth_subsingleton _ _
    · exact manifoldSmooth_subsingleton_model _ _ continuous_of_discreteTopology.continuousOn
    · exact manifoldSmooth_subsingleton_model _ _ continuous_of_discreteTopology.continuousOn
  paracompact := inferInstance
  exp := fun _ => 0
  exp_smooth := manifoldSmooth_subsingleton_model _ _ continuousOn_const
  exp_zero := rfl
  exp_line := by intros; simp
  exp_tangent := by
    intro x
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => x)
      (𝓝[≠] (0 : ℝ)) (𝓝 x)) using 1

end GaugeDiscreteAux
end

section

open Set TopologicalSpace CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

namespace GaugeNonflasqueAux
open QAlgorithms.Papers.Independent.Intakenext100.P16
open OrdinalBorelAux OrdinalTailCubeAux
universe u w

lemma global_section_borel {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {A : Type w} [TopologicalSpace A]
    (s : (measurableFunctionSheaf (TopCat.of X) A).obj.obj (op ⊤)) :
    @Measurable X A (borel X) (borel A) (fun x => s.val ⟨x,by trivial⟩) := by
  apply BorelLocalCompactAux.measurable_of_locallyBorel
  intro x
  obtain ⟨V,hx,i,hi⟩ := s.property ⟨x,by trivial⟩
  refine ⟨V,V.isOpen,hx,?_⟩
  change @Measurable V A (borel V) (borel A)
    (fun y => s.val ⟨y.val,i.le y.property⟩) at hi
  exact hi

lemma not_flasque {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {A : Type w} [TopologicalSpace A]
    (e : X ≃ₜ Cube) (a : A ≃ₜ ZMod 2) :
    ¬ TopCat.Sheaf.IsFlasque (measurableFunctionSheaf (TopCat.of X) A) := by
  classical
  obtain ⟨s,hs⟩ := OrdinalBorelAux.exists_nonborel
  let U : Opens (TopCat.of X) :=
    ⟨e ⁻¹' ({0}ᶜ : Set Cube),isClosed_singleton.isOpen_compl.preimage e.continuous⟩
  let f : (measurableFunctionSheaf (TopCat.of X) A).obj.obj (op U) := by
    refine ⟨fun x => a.symm (badFunction s (e x)),?_⟩
    intro x
    obtain ⟨b,hb⟩ := exists_slice (show e x ≠ 0 from x.property)
    let V : Opens (TopCat.of X) := ⟨e ⁻¹' slice b,(slice_open b).preimage e.continuous⟩
    have hVU : V ≤ U := fun y hy => slice_ne_zero hy
    refine ⟨V,hb,homOfLE hVU,?_⟩
    have hc : Continuous (fun y : V => (⟨e y,y.property⟩ : slice b)) :=
      (e.continuous.comp continuous_subtype_val).subtype_mk _
    exact a.symm.continuous.borel_measurable.comp
      ((badFunction_slice_measurable s b).comp hc.borel_measurable)
  intro hF
  letI := hF
  let i : U ⟶ ⊤ := homOfLE le_top
  have hsur := (CategoryTheory.epi_iff_surjective
    ((measurableFunctionSheaf (TopCat.of X) A).obj.map i.op)).mp (hF.epi i.op)
  obtain ⟨g,hg⟩ := hsur f
  let g' : X → A := fun x => g.val ⟨x,by trivial⟩
  have hgm : @Measurable X A (borel X) (borel A) g' := global_section_borel g
  have hext (x : U) : g' x = a.symm (badFunction s (e x)) := by
    have hh := congrArg (fun z => z.val x) hg
    exact hh
  letI : MeasurableSpace CountableOrd := borel CountableOrd
  haveI : BorelSpace CountableOrd := ⟨rfl⟩
  letI : MeasurableSpace (ZMod 2) := borel (ZMod 2)
  haveI : BorelSpace (ZMod 2) := ⟨rfl⟩
  have hm : @Measurable CountableOrd (ZMod 2) (borel CountableOrd) (borel (ZMod 2))
      (fun z => a (g' (e.symm (tail z)))) :=
    a.continuous.borel_measurable.comp
      (hgm.comp (e.symm.continuous.comp tail_continuous).borel_measurable)
  have he (z : CountableOrd) : a (g' (e.symm (tail z))) = badFunction s (tail z) := by
    have hz : e.symm (tail z) ∈ U := by
      change e (e.symm (tail z)) ≠ 0
      simpa only [e.apply_symm_apply] using tail_ne_zero z
    rw [hext ⟨_,hz⟩]
    simp
  apply hs
  have hh := hm (measurableSet_singleton 1)
  convert hh using 1
  ext z
  simp [he,badFunction_tail]

end GaugeNonflasqueAux
end

section

open Set TopologicalSpace CategoryTheory Opposite Filter Topology
set_option backward.isDefEq.respectTransparency false

namespace GaugeCounterexampleAux
open QAlgorithms.Papers.Independent.Intakenext100.P16
open OrdinalTailCubeAux
universe u v w

def cubeGroupHomeomorph : Multiplicative Cube ≃ₜ Cube where
  toEquiv := Multiplicative.toAdd
  continuous_toFun := continuous_toAdd
  continuous_invFun := continuous_ofAdd

theorem not_universal : ¬ (∀
    (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (E : Type v) [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    (A : Type w) [AddCommGroup A] [TopologicalSpace A] [ChartedSpace E A]
    (_coeff : FrechetAbelianLieData E A) (p : ℕ),
    TopCat.Sheaf.IsFlasque
      (measurableFunctionSheaf (TopCat.of (Fin p → G)) A)) := by
  intro h
  let G := ULift.{u} (Multiplicative Cube)
  let A := ULift.{w} (ZMod 2)
  letI : T2Space (Multiplicative Cube) := inferInstanceAs (T2Space Cube)
  letI : T2Space G := inferInstance
  letI : ChartedSpace PUnit.{v+1} A := ChartedSpace.ofDiscreteTopology
  have hF := h G PUnit.{v+1} A (GaugeDiscreteAux.discreteCoefficient A) 1
  let e : (Fin 1 → G) ≃ₜ Cube :=
    (Homeomorph.funUnique (Fin 1) G).trans (Homeomorph.ulift.trans cubeGroupHomeomorph)
  exact GaugeNonflasqueAux.not_flasque e Homeomorph.ulift hF

end GaugeCounterexampleAux
end

open QAlgorithms.Papers.Independent.Intakenext100.P16
theorem solution : ¬ (∀
    (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (E : Type) [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    (A : Type) [AddCommGroup A] [TopologicalSpace A] [ChartedSpace E A]
    (_coeff : FrechetAbelianLieData E A) (p : ℕ),
    TopCat.Sheaf.IsFlasque
      (measurableFunctionSheaf (TopCat.of (Fin p → G)) A)) :=
  GaugeCounterexampleAux.not_universal

#print axioms solution
