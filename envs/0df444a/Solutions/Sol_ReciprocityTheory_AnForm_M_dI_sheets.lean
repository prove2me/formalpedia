-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_sheets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:58.109907+00:00
-- url     : https://prove2.me/submissions/963f9d01-ccd5-49dc-95f3-6b4b51848cf2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, ∃ j : Fin d → Fin B.n, (∀ i, IsOpen (W i)) ∧
        Pairwise (Function.onFun Disjoint W) ∧ h ⁻¹' V = ⋃ i, W i ∧
        ∀ i, Set.BijOn h (W i) V ∧ W i ⊆ (B.chart (j i)).source := by
  have hO : ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ Disjoint O S := by
    obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hd.1 x
    have hex : ∃ i, f i x ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hm : x ∈ {y ∈ W | ∀ i, f i y = 0} := ⟨hxW, hc⟩
      rw [← hSW] at hm
      exact hx hm.1
    obtain ⟨i, hi⟩ := hex
    obtain ⟨j, hj⟩ := A.cover x
    have hcont : ContinuousAt (f i) x := by
      have h1 : AnalyticAt ℂ (f i ∘ (A.chart j).symm) (A.chart j x) :=
        hf i j (A.chart j x) ⟨(A.chart j).map_source hj, by
          simp only [Set.mem_preimage, (A.chart j).left_inv hj]; exact hxW⟩
      have h2 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ A.chart j) x :=
        h1.continuousAt.comp ((A.chart j).continuousAt hj)
      refine h2.congr ?_
      filter_upwards [(A.chart j).eventually_left_inverse hj] with w hw
      simp only [Function.comp_apply, hw]
    have hne : f i ⁻¹' {0}ᶜ ∈ 𝓝 x :=
      hcont.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hi)
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.mp hne
    refine ⟨t ∩ W, hto.inter hWo, ⟨hxt, hxW⟩, Set.disjoint_left.mpr ?_⟩
    rintro w ⟨hwt, hwW⟩ hwS
    have hw2 : w ∈ S ∩ W := ⟨hwS, hwW⟩
    rw [hSW] at hw2
    exact ht hwt (hw2.2 i)
  have loc : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ (h y ∉ S →
      ∃ j, U ⊆ (B.chart j).source ∧ Set.InjOn h U ∧
        ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U')) := by
    intro y
    by_cases hyS : h y ∈ S
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun h' => absurd hyS h'⟩
    obtain ⟨j, hj⟩ := B.cover y
    obtain ⟨k, hk⟩ := A.cover (h y)
    have hzt : B.chart j y ∈ (B.chart j).target := (B.chart j).map_source hj
    have hzy : (B.chart j).symm (B.chart j y) = y := (B.chart j).left_inv hj
    set φ : (Fin e → ℂ) → (Fin e → ℂ) := A.chart k ∘ h ∘ (B.chart j).symm with hφ
    have han : AnalyticAt ℂ φ (B.chart j y) :=
      hh.2 j k (B.chart j y) ⟨hzt, by simp only [Set.mem_preimage, hzy]; exact hk⟩
    have hdet := hd.2.2.2.2.2 j k (B.chart j y) hzt (by rw [hzy]; exact hyS) (by rw [hzy]; exact hk)
    let L := (LinearMap.equivOfDetNeZero
      (fderiv ℂ φ (B.chart j y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hdet).toContinuousLinearEquiv
    have hL : HasStrictFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (B.chart j y) := by
      have hLe : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ φ (B.chart j y) :=
        ContinuousLinearMap.ext fun v => rfl
      rw [hLe]
      exact han.hasStrictFDerivAt
    let P := hL.toOpenPartialHomeomorph φ
    have hPc : (P : (Fin e → ℂ) → (Fin e → ℂ)) = φ := hL.toOpenPartialHomeomorph_coe
    have hPs : B.chart j y ∈ P.source := hL.mem_toOpenPartialHomeomorph_source
    let U := (B.chart j).source ∩ (B.chart j) ⁻¹' P.source ∩ h ⁻¹' (A.chart k).source
    have hUo : IsOpen U := ((B.chart j).isOpen_inter_preimage P.open_source).inter
      (hh.1.isOpen_preimage _ (A.chart k).open_source)
    have key : ∀ y' ∈ U, (A.chart k).symm (P (B.chart j y')) = h y' := by
      intro y' hy'
      have e1 := (B.chart j).left_inv hy'.1.1
      have e2 := (A.chart k).left_inv (show h y' ∈ (A.chart k).source from hy'.2)
      rw [hPc, hφ]
      simp only [Function.comp_apply, e1, e2]
    have hinj : Set.InjOn h U := by
      intro y1 h1 y2 h2 he
      have hP : P (B.chart j y1) = P (B.chart j y2) := by
        rw [hPc, hφ]
        simp only [Function.comp_apply, (B.chart j).left_inv h1.1.1, (B.chart j).left_inv h2.1.1, he]
      exact (B.chart j).injOn h1.1.1 h2.1.1 (P.injOn h1.1.2 h2.1.2 hP)
    have hopen : ∀ U' ⊆ U, IsOpen U' → IsOpen (h '' U') := by
      intro U' hU' hU'o
      have e : h '' U' = (A.chart k).symm '' (P '' ((B.chart j) '' U')) := by
        rw [Set.image_image, Set.image_image]
        exact Set.image_congr fun y' hy' => (key y' (hU' hy')).symm
      rw [e]
      have o1 : IsOpen ((B.chart j) '' U') :=
        (B.chart j).isOpen_image_of_subset_source hU'o (fun y' hy' => (hU' hy').1.1)
      have s1 : (B.chart j) '' U' ⊆ P.source := by
        rintro _ ⟨y', hy', rfl⟩
        exact (hU' hy').1.2
      have o2 : IsOpen (P '' ((B.chart j) '' U')) := P.isOpen_image_of_subset_source o1 s1
      have s2 : P '' ((B.chart j) '' U') ⊆ (A.chart k).symm.source := by
        rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        rw [OpenPartialHomeomorph.symm_source, hPc, hφ]
        simp only [Function.comp_apply, (B.chart j).left_inv (hU' hy').1.1]
        exact (A.chart k).map_source (hU' hy').2
      exact (A.chart k).symm.isOpen_image_of_subset_source o2 s2
    exact ⟨U, hUo, ⟨⟨hj, hPs⟩, hk⟩, fun _ => ⟨j, fun y' hy' => hy'.1.1, hinj, hopen⟩⟩
  choose U hUo hyU hUp using loc
  set F := h ⁻¹' {x} with hFdef
  have hFS : ∀ y ∈ F, h y ∉ S := fun y hy => by rw [show h y = x from hy]; exact hx
  have hFc : IsCompact F := (isClosed_singleton.preimage hh.1).isCompact
  obtain ⟨t, htF, hFt⟩ := hFc.elim_nhds_subcover U (fun y _ => (hUo y).mem_nhds (hyU y))
  have hFfin : F.Finite := by
    refine t.finite_toSet.subset ?_
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hFt hz)
    obtain ⟨_, _, hinj, _⟩ := hUp y (hFS y (htF y hy))
    have hzy' : z = y := hinj hzy (hyU y)
      (by rw [show h z = x from hz, show h y = x from htF y hy])
    rw [hzy']
    exact hy
  have hcard : hFfin.toFinset.card = d := by
    rw [← Set.ncard_eq_toFinset_card F hFfin]
    exact hd.2.2.2.2.1 x hx
  subst hcard
  classical
  let σ : Fin hFfin.toFinset.card → Y := fun i => (hFfin.toFinset.equivFin.symm i : Y)
  have hσF : ∀ i, σ i ∈ F := fun i => hFfin.mem_toFinset.mp (hFfin.toFinset.equivFin.symm i).2
  have hσinj : Function.Injective σ := fun a b hab =>
    hFfin.toFinset.equivFin.symm.injective (Subtype.ext hab)
  have hσsurj : ∀ y ∈ F, ∃ i, σ i = y := fun y hy =>
    ⟨hFfin.toFinset.equivFin ⟨y, hFfin.mem_toFinset.mpr hy⟩, by simp [σ]⟩
  obtain ⟨Sep, hSep, hSepD⟩ := hFfin.t2_separation
  let G : Fin hFfin.toFinset.card → Set Y := fun i => U (σ i) ∩ Sep (σ i)
  have hGo : ∀ i, IsOpen (G i) := fun i => (hUo _).inter (hSep _).2
  have hGm : ∀ i, σ i ∈ G i := fun i => ⟨hyU _, (hSep _).1⟩
  have hGd : ∀ a b, a ≠ b → Disjoint (G a) (G b) := by
    intro a b hab
    have hab' := hSepD (hσF a) (hσF b) (hσinj.ne hab)
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right hab'
  have hGp : ∀ i, ∃ j, G i ⊆ (B.chart j).source ∧ Set.InjOn h (G i) ∧ IsOpen (h '' G i) := by
    intro i
    obtain ⟨j, hj, hinj, hop⟩ := hUp (σ i) (hFS _ (hσF i))
    exact ⟨j, Set.inter_subset_left.trans hj, hinj.mono Set.inter_subset_left,
      hop _ Set.inter_subset_left (hGo i)⟩
  choose jj hjj hGinj hGop using hGp
  obtain ⟨k, hk⟩ := A.cover x
  obtain ⟨O, hOo, hxO, hOS⟩ := hO
  let K := (⋃ i, G i)ᶜ
  have hKc : IsCompact K := (isOpen_iUnion hGo).isClosed_compl.isCompact
  have hhK : IsClosed (h '' K) := (hKc.image hh.1).isClosed
  have hxK : x ∉ h '' K := by
    rintro ⟨y, hyK, hyx⟩
    obtain ⟨i, rfl⟩ := hσsurj y hyx
    exact hyK (Set.mem_iUnion.mpr ⟨i, hGm i⟩)
  let V := (A.chart k).source ∩ O ∩ (h '' K)ᶜ ∩ ⋂ i, h '' G i
  have hVo : IsOpen V := (((A.chart k).open_source.inter hOo).inter hhK.isOpen_compl).inter
    (isOpen_iInter_of_finite hGop)
  have hxV : x ∈ V := ⟨⟨⟨hk, hxO⟩, hxK⟩, Set.mem_iInter.mpr fun i => ⟨σ i, hGm i, hσF i⟩⟩
  refine ⟨V, hVo, hxV, Set.disjoint_left.mpr fun v hv hvS => Set.disjoint_left.mp hOS hv.1.1.2 hvS,
    k, fun v hv => hv.1.1.1, fun i => G i ∩ h ⁻¹' V, jj,
    fun i => (hGo i).inter (hh.1.isOpen_preimage _ hVo),
    fun a b hab => Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hGd a b hab), ?_,
    fun i => ⟨⟨fun y hy => hy.2, (hGinj i).mono Set.inter_subset_left, fun v hv => ?_⟩,
      Set.inter_subset_left.trans (hjj i)⟩⟩
  · ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      have hyG : y ∈ ⋃ i, G i := by
        by_contra hc
        exact hy.1.2 ⟨y, hc, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyG
      exact ⟨i, hi, hy⟩
    · rintro ⟨i, _, hy⟩
      exact hy
  · obtain ⟨y, hyG, rfl⟩ := Set.mem_iInter.mp hv.2 i
    exact ⟨y, ⟨hyG, hv⟩, rfl⟩
end ReciprocityTheory.AnForm.M
