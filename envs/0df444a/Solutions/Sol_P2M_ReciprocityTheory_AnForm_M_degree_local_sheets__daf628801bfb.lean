-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_degree_local_sheets__daf628801bfb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:59.964803+00:00
-- url     : https://prove2.me/submissions/c946530a-258f-4bab-8744-d31fd1a9c964

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c
import Theorems.Thm_ReciprocityTheory_AnForm_M_exists_localHomeomorph_of_isDegreeOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open FinHolAtlas Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, (∀ i, IsOpen (W i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
        h ⁻¹' V = ⋃ i, W i ∧ ∀ i, Set.BijOn h (W i) V ∧
          ∃ j : Fin B.n, W i ⊆ (B.chart j).source := by
  classical
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  have hloc : ∀ y : (h ⁻¹' {x} : Set Y), ∃ E : OpenPartialHomeomorph Y X, y.1 ∈ E.source ∧
      Set.EqOn h E E.source ∧ ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := fun y =>
    exists_localHomeomorph_of_isDegreeOff hh hd y.1
      (by rw [show h y.1 = x from y.2]; exact hx)
  choose E hEy hEeq jE hjE using hloc
  have hFc : IsCompact (h ⁻¹' {x}) := (isClosed_singleton.preimage hh.1).isCompact
  have hFfin : (h ⁻¹' {x}).Finite := by
    obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun y => (E y).source)
      (fun y => (E y).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hEy ⟨y, hy⟩⟩)
    refine (t.finite_toSet.image Subtype.val).subset ?_
    intro z hz
    obtain ⟨w, hwt, hzw⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hzx : h z = x := hz
    have hwx : h w.1 = x := w.2
    have h1 : E w w.1 = E w z := by
      rw [← hEeq w hzw, ← hEeq w (hEy w), hzx, hwx]
    exact ⟨w, hwt, (E w).injOn (hEy w) hzw h1⟩
  have : Finite (h ⁻¹' {x}) := hFfin.to_subtype
  have hcard : Nat.card (h ⁻¹' {x}) = d := by
    rw [Nat.card_coe_set_eq]; exact hd.2.2.2.2.1 x hx
  let en : Fin d ≃ (h ⁻¹' {x} : Set Y) := ((Finite.equivFin _).trans (finCongr hcard)).symm
  obtain ⟨U0, hU0, hU0d⟩ := hFfin.t2_separation
  let U : Fin d → Set Y := fun i => U0 (en i).1 ∩ (E (en i)).source
  have hUo : ∀ i, IsOpen (U i) := fun i => (hU0 _).2.inter (E _).open_source
  have hyU : ∀ i, (en i).1 ∈ U i := fun i => ⟨(hU0 _).1, hEy _⟩
  have hUd : Pairwise (Function.onFun Disjoint U) := by
    intro i i' hii'
    have hne : (en i).1 ≠ (en i').1 := fun h' => hii' (en.injective (Subtype.ext h'))
    exact (hU0d (en i).2 (en i').2 hne).mono Set.inter_subset_left Set.inter_subset_left
  have hhU : ∀ i, h '' U i = E (en i) '' U i := fun i =>
    ((hEeq (en i)).mono Set.inter_subset_right).image_eq
  have hhUo : ∀ i, IsOpen (h '' U i) := fun i => by
    rw [hhU]; exact (E _).isOpen_image_of_subset_source (hUo i) Set.inter_subset_right
  have hKc : IsCompact (⋃ i, U i)ᶜ := (isOpen_iUnion hUo).isClosed_compl.isCompact
  have hK : IsClosed (h '' (⋃ i, U i)ᶜ) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' (⋃ i, U i)ᶜ := by
    rintro ⟨z, hzK, hzx⟩
    apply hzK
    have hz : z ∈ h ⁻¹' {x} := hzx
    refine Set.mem_iUnion.2 ⟨en.symm ⟨z, hz⟩, ?_⟩
    have := hyU (en.symm ⟨z, hz⟩)
    simpa using this
  obtain ⟨k, hk⟩ := A.cover x
  let V : Set X := (⋂ i, h '' U i) ∩ (A.chart k).source ∩ (h '' (⋃ i, U i)ᶜ)ᶜ ∩ Sᶜ
  have hVo : IsOpen V :=
    (((isOpen_iInter_of_finite hhUo).inter (A.chart k).open_source).inter
      hK.isOpen_compl).inter hSc.isOpen_compl
  have hVU : ∀ i, V ⊆ h '' U i := fun i z hz => Set.mem_iInter.1 hz.1.1.1 i
  refine ⟨V, hVo, ⟨⟨⟨Set.mem_iInter.2 fun i => ⟨(en i).1, hyU i, (en i).2⟩, hk⟩, hxK⟩, hx⟩,
    Set.disjoint_left.2 fun z hz hzS => hz.2 hzS, k, fun z hz => hz.1.1.2, ?_⟩
  refine ⟨fun i => U i ∩ h ⁻¹' V, fun i => (hUo i).inter (hVo.preimage hh.1), ?_, ?_, ?_⟩
  · intro i i' hii'
    exact (hUd hii').mono Set.inter_subset_left Set.inter_subset_left
  · ext z
    constructor
    · intro hz
      have hzU : z ∈ ⋃ i, U i := by
        by_contra hc
        exact hz.1.2 ⟨z, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hzU
      exact Set.mem_iUnion.2 ⟨i, hi, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      exact hi.2
  · intro i
    refine ⟨⟨fun z hz => hz.2, ?_, ?_⟩, jE (en i), fun z hz => hjE _ hz.1.2⟩
    · intro a ha b hb hab
      apply (E (en i)).injOn ha.1.2 hb.1.2
      rw [← hEeq (en i) ha.1.2, ← hEeq (en i) hb.1.2]
      exact hab
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := hVU i hv
      exact ⟨u, ⟨hu, hv⟩, rfl⟩
end ReciprocityTheory.AnForm.M
