-- Prove2me | solution 1 for StochKolmogorov.Extinct.inequalities_5_1_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T22:51:14.981344+00:00
-- url     : https://prove2.me/submissions/71774c25-e41c-4c02-9275-41952e71fbcb

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_1
set_option autoImplicit false

/-! Child A of 732713b3: `subErgodic P X mu` is finite.
Pure measure theory from two kernel facts (both live Proved as Persist theorems):
face invariance (`kolmogorov_sde_face_invariance`) and the TV overlap on face boxes
(`kolmogorov_face_box_tv_overlap`). Every ergodic measure lives on one open face (0-1 law from
extremality); two invariant probability measures on the same open face coincide (Hahn
decomposition + TV overlap); there are finitely many faces. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct
open EthierKurtz

section ChildA
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

theorem faceOpen_measurableSet' (I : Finset (Fin n)) : MeasurableSet (Persist.faceOpen I) := by
  have e : Persist.faceOpen I = (⋂ i, {x : SDEState n | 0 ≤ x i}) ∩
      ((⋂ i ∈ (Iᶜ : Finset (Fin n)), {x : SDEState n | x i = 0}) ∩
      (⋂ i ∈ I, {x : SDEState n | 0 < x i})) := by
    ext x; simp [Persist.faceOpen, Persist.orthant]
  rw [e]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.iInter fun i =>
      (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).measurableSet
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isClosed_eq (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet
  · exact Finset.measurableSet_biInter _ fun i _ =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).measurableSet

theorem faceOpen_disjoint' {I J : Finset (Fin n)} (h : I ≠ J) :
    Disjoint (Persist.faceOpen I) (Persist.faceOpen J) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hI0, hIp⟩ ⟨-, hJ0, hJp⟩
  apply h
  ext i
  constructor
  · intro hi
    by_contra hj
    have h1 := hIp i hi
    rw [hJ0 i hj] at h1
    exact lt_irrefl _ h1
  · intro hj
    by_contra hi
    have h1 := hJp i hj
    rw [hI0 i hi] at h1
    exact lt_irrefl _ h1

theorem mem_faceOpen_self' {x : SDEState n} (hx : x ∈ orthant n) :
    x ∈ Persist.faceOpen (Finset.univ.filter fun i => 0 < x i) := by
  refine ⟨hx, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (hx i)
  · simpa using hi

theorem trans_le_one' [IsProbabilityMeasure P] (t : ℝ≥0) (x : SDEState n) (A : Set (SDEState n)) :
    trans P X t x A ≤ 1 := by
  unfold trans
  by_cases h : AEMeasurable (X x t) P
  · haveI := Measure.isProbabilityMeasure_map h
    exact prob_le_one
  · rw [Measure.map_of_not_aemeasurable h]
    simp

/-- Face invariance in kernel form, from the almost-sure path statement. -/
theorem trans_compl_face_zero
    (hface : ∀ (J : Finset (Fin n)) (x : SDEState n), x ∈ Persist.faceOpen J →
      ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ Persist.faceOpen J)
    (J : Finset (Fin n)) (x : SDEState n) (hx : x ∈ Persist.faceOpen J) (t : ℝ≥0) :
    trans P X t x (Persist.faceOpen J)ᶜ = 0 := by
  unfold trans
  by_cases h : AEMeasurable (X x t) P
  · rw [Measure.map_apply_of_aemeasurable h (faceOpen_measurableSet' J).compl]
    have h1 := hface J x hx
    rw [ae_iff] at h1
    refine measure_mono_null ?_ h1
    intro ω hω hall
    exact hω (hall t)
  · rw [Measure.map_of_not_aemeasurable h]
    simp

variable (hface : ∀ (J : Finset (Fin n)) (x : SDEState n), x ∈ Persist.faceOpen J →
      ∀ t, trans P X t x (Persist.faceOpen J)ᶜ = 0)
include hface

theorem trans_face_zero' {J : Finset (Fin n)} {x : SDEState n} (t : ℝ≥0) (hx : x ∈ orthant n)
    (hxJ : x ∉ Persist.faceOpen J) : trans P X t x (Persist.faceOpen J) = 0 := by
  have hx' := mem_faceOpen_self' hx
  have hne : (Finset.univ.filter fun i => 0 < x i) ≠ J := fun h => hxJ (h ▸ hx')
  refine measure_mono_null ?_ (hface _ x hx' t)
  intro y hy hy'
  exact (Set.disjoint_left.1 (faceOpen_disjoint' hne)) hy' hy

theorem restrict_face_lintegral {ν : Measure (SDEState n)} (hν : IsInvariant P X ν)
    (J : Finset (Fin n)) (t : ℝ≥0) {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(ν.restrict (Persist.faceOpen J)) = ν (A ∩ Persist.faceOpen J) := by
  have hF := faceOpen_measurableSet' J
  rw [← lintegral_indicator hF]
  have hor : ∀ᵐ x ∂ν, x ∈ orthant n := by
    rw [ae_iff]
    exact hν.2.1
  have hae : ((Persist.faceOpen J).indicator fun x => trans P X t x A) =ᵐ[ν]
      fun x => trans P X t x (A ∩ Persist.faceOpen J) := by
    filter_upwards [hor] with x hx
    by_cases hxF : x ∈ Persist.faceOpen J
    · rw [Set.indicator_of_mem hxF]
      have h0 := hface J x hxF t
      have h1 := measure_inter_add_sdiff (μ := trans P X t x) A hF
      have h2 : trans P X t x (A \ Persist.faceOpen J) = 0 :=
        measure_mono_null (fun y hy => hy.2) h0
      rw [h2, add_zero] at h1
      exact h1.symm
    · rw [Set.indicator_of_notMem hxF]
      exact (measure_mono_null Set.inter_subset_right (trans_face_zero' hface t hx hxF)).symm
  rw [lintegral_congr_ae hae]
  exact hν.2.2 t _ (hA.inter hF)

theorem restrict_face_compl_lintegral {ν : Measure (SDEState n)} (hν : IsInvariant P X ν)
    (J : Finset (Fin n)) (t : ℝ≥0) {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ∫⁻ x, trans P X t x A ∂(ν.restrict (Persist.faceOpen J)ᶜ) =
      ν (A ∩ (Persist.faceOpen J)ᶜ) := by
  haveI := hν.1
  have hF := faceOpen_measurableSet' J
  have h1 := lintegral_add_measure (fun x => trans P X t x A) (ν.restrict (Persist.faceOpen J))
    (ν.restrict (Persist.faceOpen J)ᶜ)
  rw [Measure.restrict_add_restrict_compl hF, hν.2.2 t A hA,
    restrict_face_lintegral hface hν J t hA] at h1
  have h2 : ν A = ν (A ∩ Persist.faceOpen J) + ν (A ∩ (Persist.faceOpen J)ᶜ) := by
    rw [← Set.sdiff_eq, measure_inter_add_sdiff A hF]
  exact ((ENNReal.add_right_inj (measure_ne_top ν _)).1 (h1.symm.trans h2))

theorem ergodic_face_zero_one {ν : Measure (SDEState n)} (hν : IsErgodic P X ν)
    (J : Finset (Fin n)) : ν (Persist.faceOpen J) = 0 ∨ ν (Persist.faceOpen J) = 1 := by
  haveI := hν.1.1
  have hF := faceOpen_measurableSet' J
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  set F := Persist.faceOpen J with hFdef
  set a := ν F with ha
  have ha_top : a ≠ ∞ := measure_ne_top _ _
  have hlt1 : a < 1 := lt_of_le_of_ne prob_le_one h1
  have hc : ν Fᶜ = 1 - a := prob_compl_eq_one_sub hF
  have hc0 : ν Fᶜ ≠ 0 := by
    rw [hc]; exact (tsub_pos_of_lt hlt1).ne'
  have hc_top : ν Fᶜ ≠ ∞ := measure_ne_top _ _
  let ν1 : Measure (SDEState n) := a⁻¹ • ν.restrict F
  let ν2 : Measure (SDEState n) := (ν Fᶜ)⁻¹ • ν.restrict Fᶜ
  have hν1F : ν1 F = 1 := by
    simp only [ν1, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hF, Set.inter_self]
    exact ENNReal.inv_mul_cancel h0 ha_top
  have inv1 : IsInvariant P X ν1 := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp only [ν1, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel h0 ha_top
    · simp only [ν1, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hF]
      rw [measure_mono_null Set.inter_subset_left hν.1.2.1, mul_zero]
    · intro t A hA
      simp only [ν1]
      rw [lintegral_smul_measure, restrict_face_lintegral hface hν.1 J t hA, Measure.smul_apply,
        Measure.restrict_apply hA]
  have inv2 : IsInvariant P X ν2 := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp only [ν2, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel hc0 hc_top
    · simp only [ν2, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hF.compl]
      rw [measure_mono_null Set.inter_subset_left hν.1.2.1, mul_zero]
    · intro t A hA
      simp only [ν2]
      rw [lintegral_smul_measure, restrict_face_compl_lintegral hface hν.1 J t hA,
        Measure.smul_apply, Measure.restrict_apply hA]
  have hpos : 0 < a.toNNReal := ENNReal.toNNReal_pos h0 ha_top
  have hlt : a.toNNReal < 1 := by
    have := (ENNReal.toNNReal_lt_toNNReal ha_top ENNReal.one_ne_top).2 hlt1
    simpa using this
  have hcoe1 : ((a.toNNReal : ℝ≥0) : ℝ≥0∞) = a := ENNReal.coe_toNNReal ha_top
  have hcoe2 : ((1 - a.toNNReal : ℝ≥0) : ℝ≥0∞) = ν Fᶜ := by
    rw [ENNReal.coe_sub, hcoe1, ENNReal.coe_one, hc]
  have hdec : ν = ((a.toNNReal : ℝ≥0) : ℝ≥0∞) • ν1 + ((1 - a.toNNReal : ℝ≥0) : ℝ≥0∞) • ν2 := by
    rw [hcoe1, hcoe2]
    simp only [ν1, ν2, smul_smul, ENNReal.mul_inv_cancel h0 ha_top,
      ENNReal.mul_inv_cancel hc0 hc_top, one_smul]
    exact (Measure.restrict_add_restrict_compl hF).symm
  have heq := hν.2 ν1 ν2 inv1 inv2 a.toNNReal hpos hlt hdec
  rw [heq] at hν1F
  exact h1 hν1F

theorem ergodic_exists_face {ν : Measure (SDEState n)} (hν : IsErgodic P X ν) :
    ∃ J : Finset (Fin n), ν (Persist.faceOpen J) = 1 := by
  haveI := hν.1.1
  by_contra hno
  have hz : ∀ J : Finset (Fin n), ν (Persist.faceOpen J) = 0 := by
    intro J
    rcases ergodic_face_zero_one hface hν J with h | h
    · exact h
    · exact absurd ⟨J, h⟩ hno
  have hsub : (Set.univ : Set (SDEState n)) ⊆
      (⋃ J : Finset (Fin n), Persist.faceOpen J) ∪ (orthant n)ᶜ := by
    intro x _
    by_cases hx : x ∈ orthant n
    · exact Or.inl (Set.mem_iUnion.2 ⟨_, mem_faceOpen_self' hx⟩)
    · exact Or.inr hx
  have h0 : ν Set.univ = 0 :=
    measure_mono_null hsub (measure_union_null (measure_iUnion_null hz) hν.1.2.1)
  rw [measure_univ] at h0
  exact one_ne_zero h0

end ChildA

section ChildA2
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

theorem tv_ge_abs (μ ν : Measure (SDEState n)) (hμ : ∀ A, μ A ≤ 1) (hν : ∀ A, ν A ≤ 1)
    {D : Set (SDEState n)} (hD : MeasurableSet D) :
    |(μ D).toReal - (ν D).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  unfold MarkovChainCLT.tvDist
  refine le_csSup ⟨1, ?_⟩ ⟨D, hD, rfl⟩
  rintro r ⟨A, -, rfl⟩
  have h1 : (μ A).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hμ A); simpa using this
  have h2 : (ν A).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hν A); simpa using this
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

theorem box_measurable (J : Finset (Fin n)) (m : ℕ) :
    MeasurableSet {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1} := by
  have e : {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1} =
      ⋂ i ∈ J, ({x : SDEState n | 1 / ((m : ℝ) + 1) ≤ x i} ∩ {x | x i ≤ (m : ℝ) + 1}) := by
    ext x; simp
  rw [e]
  exact Finset.measurableSet_biInter _ fun i _ =>
    (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).measurableSet.inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet

theorem box_mono (J : Finset (Fin n)) {m m' : ℕ} (h : m ≤ m') :
    {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1} ⊆
      {x : SDEState n | ∀ i ∈ J, 1 / ((m' : ℝ) + 1) ≤ x i ∧ x i ≤ (m' : ℝ) + 1} := by
  intro x hx i hi
  obtain ⟨h1, h2⟩ := hx i hi
  have hm : (m : ℝ) ≤ m' := Nat.cast_le.2 h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · calc 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
      _ ≤ x i := h1
  · linarith

theorem face_subset_boxes (J : Finset (Fin n)) :
    Persist.faceOpen J ⊆
      ⋃ m : ℕ, {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1} := by
  intro x hx
  obtain ⟨-, -, hpos⟩ := hx
  set s : ℝ := ∑ i ∈ J, (x i + 1 / x i) with hsdef
  have hs : ∀ i ∈ J, x i + 1 / x i ≤ s := fun i hi =>
    Finset.single_le_sum (f := fun i => x i + 1 / x i)
      (fun j hj => by have := hpos j hj; positivity) hi
  refine Set.mem_iUnion.2 ⟨⌈s⌉₊, fun i hi => ?_⟩
  have hxi := hpos i hi
  have h1 := hs i hi
  have hc : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hinv : 0 < 1 / x i := by positivity
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have h2 : 1 / x i ≤ (⌈s⌉₊ : ℝ) + 1 := by linarith
    rw [div_le_iff₀ hxi] at h2
    linarith [mul_comm (x i) ((⌈s⌉₊ : ℝ) + 1)]
  · linarith

variable (hovl : ∀ (J : Finset (Fin n)) (α β : ℝ), 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε)
include hovl

theorem invariant_face_unique [IsProbabilityMeasure P]
    {ν1 ν2 : Measure (SDEState n)} (h1 : IsInvariant P X ν1) (h2 : IsInvariant P X ν2)
    (J : Finset (Fin n)) (hF1 : ν1 (Persist.faceOpen J) = 1)
    (hF2 : ν2 (Persist.faceOpen J) = 1) : ν1 = ν2 := by
  haveI := h1.1
  haveI := h2.1
  have hF := faceOpen_measurableSet' J
  obtain ⟨D, hD, hDp, hDn⟩ := hahn_decomposition ν1 ν2
  have hle1 : ν2.restrict D ≤ ν1.restrict D := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hDp _ (hs.inter hD) Set.inter_subset_right
  have hle2 : ν1.restrict Dᶜ ≤ ν2.restrict Dᶜ := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hDn _ (hs.inter hD.compl) Set.inter_subset_right
  have e1 : ν1 = ν2.restrict D + (ν1.restrict D - ν2.restrict D) + ν1.restrict Dᶜ := by
    rw [add_comm (ν2.restrict D), Measure.sub_add_cancel_of_le hle1,
      Measure.restrict_add_restrict_compl hD]
  have e2 : ν2 = ν2.restrict D + ν1.restrict Dᶜ + (ν2.restrict Dᶜ - ν1.restrict Dᶜ) := by
    rw [add_assoc, add_comm (ν1.restrict Dᶜ), Measure.sub_add_cancel_of_le hle2,
      Measure.restrict_add_restrict_compl hD]
  have hposDc : (ν1.restrict D - ν2.restrict D) Dᶜ = 0 := by
    refine le_antisymm ((Measure.le_iff'.1 Measure.sub_le Dᶜ).trans ?_) zero_le
    rw [Measure.restrict_apply hD.compl, Set.compl_inter_self, measure_empty]
  have hnegD : (ν2.restrict Dᶜ - ν1.restrict Dᶜ) D = 0 := by
    refine le_antisymm ((Measure.le_iff'.1 Measure.sub_le D).trans ?_) zero_le
    rw [Measure.restrict_apply hD, Set.inter_compl_self, measure_empty]
  have hb1D : ν1.restrict Dᶜ D = 0 := by
    rw [Measure.restrict_apply hD, Set.inter_compl_self, measure_empty]
  have ha2D : ν2.restrict D D = ν2 D := by
    rw [Measure.restrict_apply hD, Set.inter_self]
  generalize hp : ν1.restrict D - ν2.restrict D = pos at e1 hposDc
  generalize hn : ν2.restrict Dᶜ - ν1.restrict Dᶜ = neg at e2 hnegD
  generalize hb : ν1.restrict Dᶜ = b1 at e1 e2 hb1D
  generalize ha : ν2.restrict D = a2 at e1 e2 ha2D
  have hpos_le : ∀ s, pos s ≤ ν1 s := fun s => by
    rw [e1, Measure.add_apply, Measure.add_apply]
    exact le_add_right (le_add_left le_rfl)
  have hneg_le : ∀ s, neg s ≤ ν2 s := fun s => by
    rw [e2, Measure.add_apply, Measure.add_apply]
    exact le_add_left le_rfl
  have hfin : ∀ s, a2 s + b1 s ≤ 1 := fun s => by
    have : ν2 s ≤ 1 := prob_le_one
    rw [e2, Measure.add_apply, Measure.add_apply] at this
    exact le_trans le_self_add this
  have hfin' : ∀ s, a2 s + b1 s ≠ ∞ := fun s => ne_top_of_le_ne_top ENNReal.one_ne_top (hfin s)
  have hmass : pos Set.univ = neg Set.univ := by
    have h1u : ν1 Set.univ = ν2 Set.univ := by rw [measure_univ, measure_univ]
    rw [e1, e2] at h1u
    simp only [Measure.add_apply] at h1u
    have : a2 Set.univ + b1 Set.univ + pos Set.univ = a2 Set.univ + b1 Set.univ + neg Set.univ := by
      rw [← h1u]; ring
    exact (ENNReal.add_right_inj (hfin' _)).1 this
  by_contra hne
  have hpos_ne : pos Set.univ ≠ 0 := by
    intro h0
    have hp0 : pos = 0 := Measure.measure_univ_eq_zero.1 h0
    have hn0 : neg = 0 := Measure.measure_univ_eq_zero.1 (hmass ▸ h0)
    apply hne
    rw [e1, e2, hp0, hn0, add_zero, add_zero]
  have hneg_ne : neg Set.univ ≠ 0 := by rw [← hmass]; exact hpos_ne
  have hν1Fc : ν1 (Persist.faceOpen J)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hF, hF1, tsub_self]
  have hν2Fc : ν2 (Persist.faceOpen J)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hF, hF2, tsub_self]
  have hposFc : pos (Persist.faceOpen J)ᶜ = 0 :=
    le_antisymm ((hpos_le _).trans hν1Fc.le) zero_le
  have hnegFc : neg (Persist.faceOpen J)ᶜ = 0 :=
    le_antisymm ((hneg_le _).trans hν2Fc.le) zero_le
  have hbox : ∀ μ : Measure (SDEState n), μ (Persist.faceOpen J)ᶜ = 0 → μ Set.univ ≠ 0 →
      ∃ m : ℕ, μ (Persist.faceOpen J ∩
        {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1}) ≠ 0 := by
    intro μ hμc hμu
    by_contra hcon
    have hz : ∀ m : ℕ, μ (Persist.faceOpen J ∩
        {x : SDEState n | ∀ i ∈ J, 1 / ((m : ℝ) + 1) ≤ x i ∧ x i ≤ (m : ℝ) + 1}) = 0 :=
      fun m => by by_contra h; exact hcon ⟨m, h⟩
    have hF0 : μ (Persist.faceOpen J) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hz)
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (face_subset_boxes J hx)
      exact Set.mem_iUnion.2 ⟨m, hx, hm⟩
    apply hμu
    exact measure_mono_null (fun x _ => by
      by_cases hx : x ∈ Persist.faceOpen J
      · exact Or.inl hx
      · exact Or.inr hx) (measure_union_null hF0 hμc)
  obtain ⟨m1, hm1⟩ := hbox pos hposFc hpos_ne
  obtain ⟨m2, hm2⟩ := hbox neg hnegFc hneg_ne
  set M := max m1 m2 with hM
  set S0 := Persist.faceOpen J ∩
    {x : SDEState n | ∀ i ∈ J, 1 / ((M : ℝ) + 1) ≤ x i ∧ x i ≤ (M : ℝ) + 1} with hS0
  have hS0m : MeasurableSet S0 := hF.inter (box_measurable J M)
  have hposS0 : pos S0 ≠ 0 := fun h => hm1 (measure_mono_null
    (Set.inter_subset_inter_right _ (box_mono J (le_max_left m1 m2))) h)
  have hnegS0 : neg S0 ≠ 0 := fun h => hm2 (measure_mono_null
    (Set.inter_subset_inter_right _ (box_mono J (le_max_right m1 m2))) h)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hαβ : 1 / ((M : ℝ) + 1) ≤ (M : ℝ) + 1 := by
    have : 1 / ((M : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  obtain ⟨T, ε, hε, hT⟩ := hovl J (1 / ((M : ℝ) + 1)) ((M : ℝ) + 1) (by positivity) hαβ
  have hg1 : ∀ x, trans P X T x D ≤ 1 := fun x => trans_le_one' (P := P) (X := X) T x D
  have hgtop : ∀ x, trans P X T x D ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 x)
  set c : ℝ≥0∞ := ENNReal.ofReal (1 - ε) with hc
  have hgap : ∀ x ∈ S0, ∀ y ∈ S0, trans P X T x D ≤ trans P X T y D + c := by
    intro x hx y hy
    have htv := hT x hx.1 hx.2 y hy.1 hy.2
    have habs := tv_ge_abs (trans P X T x) (trans P X T y) (trans_le_one' (P := P) (X := X) T x)
      (trans_le_one' (P := P) (X := X) T y) hD
    have hreal : (trans P X T x D).toReal ≤ (trans P X T y D).toReal + (1 - ε) := by
      have := le_abs_self ((trans P X T x D).toReal - (trans P X T y D).toReal)
      linarith
    calc trans P X T x D = ENNReal.ofReal (trans P X T x D).toReal :=
          (ENNReal.ofReal_toReal (hgtop x)).symm
      _ ≤ ENNReal.ofReal ((trans P X T y D).toReal + (1 - ε)) := ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (trans P X T y D).toReal + ENNReal.ofReal (1 - ε) :=
          ENNReal.ofReal_add_le
      _ = trans P X T y D + c := by rw [ENNReal.ofReal_toReal (hgtop y)]
  -- invariance at time T for the Hahn set D
  have hI1 := (h1.2.2 T D hD).symm
  have hI2 := (h2.2.2 T D hD).symm
  rw [e1] at hI1
  rw [e2] at hI2
  rw [lintegral_add_measure, lintegral_add_measure, Measure.add_apply, Measure.add_apply,
    hb1D, add_zero] at hI1 hI2
  rw [hnegD, add_zero, ha2D] at hI2
  rw [ha2D] at hI1
  set Za := ∫⁻ x, trans P X T x D ∂a2
  set Zb := ∫⁻ x, trans P X T x D ∂b1
  set Ip := ∫⁻ x, trans P X T x D ∂pos
  set In := ∫⁻ x, trans P X T x D ∂neg
  have hA2 : ν2 D ≠ ∞ := measure_ne_top _ _
  have hpD : pos D ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν1 D) (hpos_le D)
  have hZ : Za + Zb ≠ ∞ := by
    have : Za + Zb ≤ ν2 D := by
      calc Za + Zb ≤ Za + Zb + In := le_self_add
        _ = ν2 D := hI2.symm
    exact ne_top_of_le_ne_top hA2 this
  have key : Za + Zb + Ip = Za + Zb + (In + pos D) := by
    calc Za + Zb + Ip = Za + Ip + Zb := by ring
      _ = ν2 D + pos D := hI1.symm
      _ = Za + Zb + In + pos D := by rw [hI2]
      _ = Za + Zb + (In + pos D) := by ring
  have hIp : Ip = In + pos D := (ENNReal.add_right_inj hZ).1 key
  have hposU : pos Set.univ = pos D := by
    rw [← measure_add_measure_compl hD, hposDc, add_zero]
  have hIp_le : Ip ≤ pos Set.univ := by
    calc Ip ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂pos := lintegral_mono fun x => hg1 x
      _ = pos Set.univ := lintegral_one
  have hIn : In = 0 := by
    have h3 : In + pos D ≤ 0 + pos D := by rw [zero_add, ← hIp, ← hposU]; exact hIp_le
    exact le_antisymm ((ENNReal.add_le_add_iff_right hpD).1 h3) zero_le
  have hIpU : Ip = pos Set.univ := by rw [hIp, hIn, zero_add, hposU]
  set a : ℝ≥0∞ := ⨅ y ∈ S0, trans P X T y D with ha_def
  have hlow : ∀ y ∈ S0, a ≤ trans P X T y D := fun y hy => iInf₂_le y hy
  have hup : ∀ x ∈ S0, trans P X T x D ≤ a + c := by
    intro x hx
    have h4 : trans P X T x D - c ≤ a :=
      le_iInf₂ fun y hy => tsub_le_iff_right.2 (hgap x hx y hy)
    calc trans P X T x D ≤ trans P X T x D - c + c := le_tsub_add
      _ ≤ a + c := add_le_add h4 le_rfl
  have ha0 : a = 0 := by
    have h5 : a * neg S0 ≤ In := by
      calc a * neg S0 = ∫⁻ x, S0.indicator (fun _ => a) x ∂neg :=
            (lintegral_indicator_const hS0m a).symm
        _ ≤ In := lintegral_mono fun x => by
            by_cases hx : x ∈ S0
            · rw [Set.indicator_of_mem hx]; exact hlow x hx
            · rw [Set.indicator_of_notMem hx]; exact zero_le
    rw [hIn, nonpos_iff_eq_zero, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exact h5
    · exact absurd h5 hnegS0
  have hupper : Ip ≤ (a + c) * pos S0 + 1 * pos S0ᶜ := by
    calc Ip ≤ ∫⁻ x, (S0.indicator (fun _ => a + c) x + S0ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x)
          ∂pos := lintegral_mono fun x => by
            by_cases hx : x ∈ S0
            · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hx), add_zero]
              exact hup x hx
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (show x ∈ S0ᶜ from hx),
                zero_add]
              exact hg1 x
      _ = (a + c) * pos S0 + 1 * pos S0ᶜ := by
          rw [lintegral_add_left (measurable_const.indicator hS0m), lintegral_indicator_const hS0m,
            lintegral_indicator_const hS0m.compl]
  rw [hIpU, ← measure_add_measure_compl hS0m, one_mul, ha0, zero_add] at hupper
  have hS0top : pos S0 ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν1 S0) (hpos_le S0)
  have hSc : pos S0ᶜ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν1 _) (hpos_le _)
  have h6 : pos S0 ≤ c * pos S0 := (ENNReal.add_le_add_iff_right hSc).1 hupper
  have hc1 : c < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  have h7 : c * pos S0 < 1 * pos S0 := ENNReal.mul_lt_mul_left hposS0 hS0top hc1
  rw [one_mul] at h7
  exact absurd (lt_of_le_of_lt h6 h7) (lt_irrefl _)

end ChildA2

/-- Child A: finitely many ergodic measures, hence `subErgodic P X mu` is finite. -/
theorem subErgodic_finite_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : ∀ (J : Finset (Fin n)) (x : SDEState n), x ∈ Persist.faceOpen J →
      ∀ t, trans P X t x (Persist.faceOpen J)ᶜ = 0)
    (hovl : ∀ (J : Finset (Fin n)) (α β : ℝ), 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε)
    (mu : Measure (SDEState n)) : (subErgodic P X mu).Finite := by
  classical
  have hE : {ν : Measure (SDEState n) | IsErgodic P X ν}.Finite := by
    let φ : Measure (SDEState n) → Finset (Fin n) := fun ν =>
      if h : IsErgodic P X ν then Classical.choose (ergodic_exists_face hface h) else ∅
    have hinj : Set.InjOn φ {ν | IsErgodic P X ν} := by
      intro ν1 h1 ν2 h2 heq
      have h1' : IsErgodic P X ν1 := h1
      have h2' : IsErgodic P X ν2 := h2
      have e1 := Classical.choose_spec (ergodic_exists_face hface h1')
      have e2 := Classical.choose_spec (ergodic_exists_face hface h2')
      simp only [φ, dif_pos h1', dif_pos h2'] at heq
      rw [heq] at e1
      exact invariant_face_unique hovl h1'.1 h2'.1 _ e1 e2
    exact Set.Finite.of_finite_image (Set.toFinite _) hinj
  exact hE.subset fun ν hν => hν.1.1

end StochKolmogorov.Extinct

/-! Child D of 732713b3 (inequalities (5.1)-(5.2)): the finite minimax assembly.
From finiteness of `subErgodic`, vanishing supported exponents and integrability, the weights
`phat`, `pcheck` and the margin `ρe` of (5.1)-(5.2) exist (finite Hahn-Banach separation). -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct
open EthierKurtz

/-- Finite minimax: if every convex combination of the finitely many vectors `v a` has a positive
coordinate, a nonnegative weight vector `q` gives all of them a uniform positive margin. -/
theorem minimax_finite {n : ℕ} {α : Type*} (S : Finset α) (v : α → Fin n → ℝ)
    (h : ∀ w : α → ℝ, (∀ a ∈ S, 0 ≤ w a) → ∑ a ∈ S, w a = 1 →
      ∃ j, 0 < ∑ a ∈ S, w a * v a j) :
    ∃ q : Fin n → ℝ, (∀ j, 0 ≤ q j) ∧ ∃ m : ℝ, 0 < m ∧ ∀ a ∈ S, m < ∑ j, q j * v a j := by
  classical
  let L : (S → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun w => ∑ a : S, w a • v a
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul] }
  have hLapp : ∀ w j, L w j = ∑ a : S, w a * v a j := by
    intro w j; simp [L, Finset.sum_apply]
  let K : Set (Fin n → ℝ) := L '' stdSimplex ℝ S
  let N : Set (Fin n → ℝ) := {y | ∀ j, y j ≤ 0}
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ S).linear_image L
  have hKk : IsCompact K :=
    (isCompact_stdSimplex (𝕜 := ℝ) S).image (LinearMap.continuous_of_finiteDimensional L)
  have hNc : Convex ℝ N := by
    intro x hx y hy a b ha hb _ j
    show a * x j + b * y j ≤ 0
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx j))
      (mul_nonpos_of_nonneg_of_nonpos hb (hy j))
  have hNcl : IsClosed N := by
    have : N = ⋂ j, {y : Fin n → ℝ | y j ≤ 0} := by ext y; simp [N]
    rw [this]
    exact isClosed_iInter fun j => isClosed_le (continuous_apply j) continuous_const
  have hdisj : Disjoint K N := by
    rw [Set.disjoint_left]
    rintro y ⟨w, hw, rfl⟩ hyN
    let w' : α → ℝ := fun a => if ha : a ∈ S then w ⟨a, ha⟩ else 0
    have hconv : ∀ g : α → ℝ, ∑ a ∈ S, w' a * g a = ∑ a : S, w a * g a := by
      intro g
      rw [← Finset.sum_coe_sort S]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [w']
    obtain ⟨j, hj⟩ := h w' (by intro a ha; simp [w', ha, hw.1]) (by
      have := hconv (fun _ => 1)
      simp only [mul_one] at this
      rw [this]; exact hw.2)
    have h1 := hyN j
    rw [hLapp, ← hconv (fun a => v a j)] at h1
    linarith
  obtain ⟨f, u, u', hfK, huu, hfN⟩ := geometric_hahn_banach_compact_closed hKc hKk hNc hNcl hdisj
  have hu' : u' < 0 := by
    have := hfN 0 (fun j => le_refl 0)
    simpa using this
  let q : Fin n → ℝ := fun j => -f (Pi.single j 1)
  have hq : ∀ j, 0 ≤ q j := by
    intro j
    by_contra hneg
    have hneg' : q j < 0 := lt_of_not_ge hneg
    have hfe : 0 < f (Pi.single j 1) := by simp only [q] at hneg'; linarith
    let t : ℝ := -u' / f (Pi.single j 1) + 1
    have ht : 0 ≤ t := by
      have : 0 ≤ -u' / f (Pi.single j 1) := div_nonneg (by linarith) hfe.le
      simp only [t]; linarith
    have hyN : ((-t) • Pi.single j (1 : ℝ)) ∈ N := by
      intro k
      by_cases hk : k = j
      · subst hk; simp; linarith
      · simp [hk]
    have h1 := hfN _ hyN
    rw [map_smul, smul_eq_mul] at h1
    have h2 : t * f (Pi.single j 1) = -u' + f (Pi.single j 1) := by
      simp only [t]; field_simp
    linarith
  have hrep : ∀ x : Fin n → ℝ, f x = -∑ j, q j * x j := by
    intro x
    have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, q, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨q, hq, -u, by linarith, ?_⟩
  intro a ha
  have hmem : v a ∈ K := by
    refine ⟨Pi.single ⟨a, ha⟩ 1, single_mem_stdSimplex ℝ _, ?_⟩
    ext j
    rw [hLapp]
    simp [Pi.single_apply]
  have := hfK _ hmem
  rw [hrep] at this
  linarith

/-- An element of `subErgodic mu` forces `supp mu ≠ ∅` (otherwise `∂ℝ^mu₊ = ∅`). -/
theorem supp_nonempty_of_subErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {mu ν : Measure (SDEState n)}
    (h : ν ∈ subErgodic P X mu) : (supp mu).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  obtain ⟨⟨⟨⟨hprob, -, -⟩, -⟩, -⟩, h0⟩ := h
  have hc : (faceBdry mu)ᶜ = Set.univ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_univ, iff_true]
    rintro ⟨hx, hx'⟩
    exact hx' ⟨hx, fun i hi => by simp [hne] at hi⟩
  rw [hc, measure_univ] at h0
  exact one_ne_zero h0

theorem exists_pos_lower {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (g : Fin n → ℝ)
    (h : ∀ i, P i → 0 < g i) : ∃ c : ℝ, 0 < c ∧ ∀ i, P i → c ≤ g i := by
  rcases (Finset.univ.filter P).eq_empty_or_nonempty with h0 | hne
  · refine ⟨1, one_pos, fun i hi => ?_⟩
    have : i ∈ Finset.univ.filter P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    rw [h0] at this
    exact absurd this (Finset.notMem_empty _)
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ g hne
    exact ⟨g i0, h i0 (Finset.mem_filter.1 hi0).2,
      fun i hi => hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)⟩

/-- Child D: the conclusion of (5.1)-(5.2) from finiteness of `subErgodic`, vanishing supported
exponents of `mu` and Assumption 1.3 (integrability is forced by the positive exponents). -/
theorem childD_minimax_assembly {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (hfin : (subErgodic P X mu).Finite)
    (hz : ∀ j ∈ supp mu, lyap C j mu = 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ phat : Fin n → ℝ, (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀ ∧
      ∃ pcheck : ℝ, 0 < pcheck ∧ pcheck < δ₀ ∧
      ∃ ρe : ℝ, 0 < ρe ∧
        ∀ ν : Measure (SDEState n), (ν ∈ subErgodic P X mu ∨ ν = mu) →
          ∀ i : Fin n, i ∉ supp mu →
            3 * ρe < (∑ j ∈ supp mu, phat j * lyap C j ν) - pcheck * lyap C i ν := by
  classical
  set I := supp mu with hI
  set S := hfin.toFinset with hS
  have hmemS : ∀ ν, ν ∈ S ↔ ν ∈ subErgodic P X mu := fun ν => hfin.mem_toFinset
  obtain ⟨q, hq, m, hm, hqm⟩ := minimax_finite S (fun ν j => if j ∈ I then lyap C j ν else 0) (by
    intro w hw0 hw1
    have hSne : S.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero)
    obtain ⟨ν0, hν0⟩ := hSne
    have hIne : I.Nonempty := supp_nonempty_of_subErgodic ((hmemS ν0).1 hν0)
    set s := S.filter (fun a => 0 < w a) with hs
    have hsS : ∀ a ∈ s, a ∈ S := fun a ha => (Finset.mem_filter.1 ha).1
    have hws : ∑ a ∈ s, w a = 1 := by
      rw [hs, Finset.sum_filter_of_ne fun a ha hne => lt_of_le_of_ne (hw0 a ha) (Ne.symm hne)]
      exact hw1
    have hconv : (∑ a ∈ s, ((w a).toNNReal : ℝ≥0∞) • a) ∈ conv (subErgodic P X mu) := by
      refine ⟨s, fun a => (w a).toNNReal, ?_, ?_, ?_, rfl⟩
      · intro a ha
        exact (hmemS a).1 (hsS a (Finset.mem_coe.1 ha))
      · intro a ha
        exact Real.toNNReal_pos.2 (Finset.mem_filter.1 ha).2
      · apply NNReal.coe_injective
        rw [NNReal.coe_sum, NNReal.coe_one, ← hws]
        exact Finset.sum_congr rfl fun a ha => Real.coe_toNNReal _ (hw0 a (hsS a ha))
    obtain ⟨j, hjI, hj⟩ := h13.2.2 hIne _ hconv
    refine ⟨j, ?_⟩
    have hlin : lyap C j (∑ a ∈ s, ((w a).toNNReal : ℝ≥0∞) • a)
        = ∑ a ∈ s, w a * lyap C j a := by
      have hintπ : Integrable (fun x => C.f j x - C.sig j j * C.g j x ^ 2 / 2)
          (∑ a ∈ s, ((w a).toNNReal : ℝ≥0∞) • a) := by
        by_contra hni
        have h0 : lyap C j (∑ a ∈ s, ((w a).toNNReal : ℝ≥0∞) • a) = 0 := integral_undef hni
        rw [h0] at hj
        exact lt_irrefl _ hj
      have hinta : ∀ a ∈ s, Integrable (fun x => C.f j x - C.sig j j * C.g j x ^ 2 / 2)
          (((w a).toNNReal : ℝ≥0∞) • a) := integrable_finsetSum_measure.1 hintπ
      unfold lyap
      rw [integral_finsetSum_measure hinta]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [integral_smul_measure, ENNReal.coe_toReal, Real.coe_toNNReal _ (hw0 a (hsS a ha)),
        smul_eq_mul]
    rw [hlin] at hj
    have hsw : ∑ a ∈ S, w a * (if j ∈ I then lyap C j a else 0) = ∑ a ∈ s, w a * lyap C j a := by
      rw [Finset.sum_congr rfl (fun a _ => by rw [if_pos hjI]), hs]
      exact (Finset.sum_filter_of_ne fun a ha hne =>
        lt_of_le_of_ne (hw0 a ha) (fun h => hne (by rw [← h, zero_mul]))).symm
    rw [hsw]
    exact hj)
  have hsumI : ∀ ν, ∑ j, q j * (if j ∈ I then lyap C j ν else 0) = ∑ j ∈ I, q j * lyap C j ν := by
    intro ν
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  set A := ∑ ν ∈ S, ∑ j ∈ I, |lyap C j ν| with hA
  have hAν : ∀ ν ∈ S, ∑ j ∈ I, |lyap C j ν| ≤ A := fun ν hν =>
    Finset.single_le_sum (f := fun ν => ∑ j ∈ I, |lyap C j ν|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hν
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set η := m / (2 * (A + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηA : η * (A + 1) = m / 2 := by
    rw [hη]; field_simp
  set p : Fin n → ℝ := fun j => q j + η with hp
  have hp0 : ∀ j, 0 < p j := fun j => by have := hq j; simp only [hp]; linarith
  have hpm : ∀ ν ∈ S, m / 2 ≤ ∑ j ∈ I, p j * lyap C j ν := by
    intro ν hν
    have h1 := hqm ν hν
    rw [hsumI] at h1
    have h2 : ∑ j ∈ I, p j * lyap C j ν
        = ∑ j ∈ I, q j * lyap C j ν + η * ∑ j ∈ I, lyap C j ν := by
      simp only [hp, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : -(∑ j ∈ I, |lyap C j ν|) ≤ ∑ j ∈ I, lyap C j ν := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => neg_abs_le _
    have h4 : η * (∑ j ∈ I, |lyap C j ν|) ≤ η * A := mul_le_mul_of_nonneg_left (hAν ν hν) hη0.le
    have h7 : η * -(∑ j ∈ I, |lyap C j ν|) ≤ η * ∑ j ∈ I, lyap C j ν :=
      mul_le_mul_of_nonneg_left h3 hη0.le
    have h8 : η * -(∑ j ∈ I, |lyap C j ν|) = -(η * ∑ j ∈ I, |lyap C j ν|) := mul_neg _ _
    have h6 : η * A ≤ η * (A + 1) := by linarith
    linarith
  set T := ∑ j ∈ I, p j with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => (hp0 j).le
  set t := δ₀ / (2 * (T + 1)) with ht
  have ht0 : 0 < t := by positivity
  have htT1 : t * (T + 1) = δ₀ / 2 := by rw [ht]; field_simp
  have htT : t * T ≤ δ₀ / 2 := by linarith
  refine ⟨fun j => t * p j, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨mul_pos ht0 (hp0 i), ?_⟩
    have h1 : p i ≤ T := Finset.single_le_sum (fun j _ => (hp0 j).le) hi
    have h2 := mul_le_mul_of_nonneg_left h1 ht0.le
    linarith
  · show ∑ j ∈ I, t * p j ≤ δ₀
    rw [← Finset.mul_sum]
    linarith
  set M := t * (m / 2) with hMdef
  have hM : 0 < M := by positivity
  have hphatS : ∀ ν ∈ S, M ≤ ∑ j ∈ I, t * p j * lyap C j ν := by
    intro ν hν
    have e : ∑ j ∈ I, t * p j * lyap C j ν = t * ∑ j ∈ I, p j * lyap C j ν := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hpm ν hν) ht0.le
  set B := ∑ ν ∈ S, ∑ i, |lyap C i ν| with hB
  have hBν : ∀ ν ∈ S, ∑ i, |lyap C i ν| ≤ B := fun ν hν =>
    Finset.single_le_sum (f := fun ν => ∑ i, |lyap C i ν|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hν
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set pc := min (δ₀ / 2) (M / (2 * (B + 1))) with hpc
  have hpc0 : 0 < pc := lt_min (by positivity) (by positivity)
  have hpcδ : pc < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hpcB : pc * (B + 1) ≤ M / 2 := by
    have h1 : pc ≤ M / (2 * (B + 1)) := min_le_right _ _
    have h2 : M / (2 * (B + 1)) * (B + 1) = M / 2 := by field_simp
    calc pc * (B + 1) ≤ M / (2 * (B + 1)) * (B + 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = M / 2 := h2
  obtain ⟨c, hc0, hc⟩ := exists_pos_lower (fun i => i ∉ I) (fun i => -lyap C i mu)
    (fun i hi => by have := h13.2.1 i hi; linarith)
  set ρ := min (M / 2) (pc * c) / 4 with hρ
  have hρ0 : 0 < ρ := div_pos (lt_min (by positivity) (mul_pos hpc0 hc0)) (by norm_num)
  refine ⟨pc, hpc0, hpcδ, ρ, hρ0, ?_⟩
  rintro ν (hν | hν) i hi
  · have hνS : ν ∈ S := (hmemS ν).2 hν
    show 3 * ρ < (∑ j ∈ I, t * p j * lyap C j ν) - pc * lyap C i ν
    have h1 := hphatS ν hνS
    have h2 : |lyap C i ν| ≤ B :=
      le_trans (Finset.single_le_sum (f := fun i => |lyap C i ν|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)) (hBν ν hνS)
    have h3 : pc * lyap C i ν ≤ pc * |lyap C i ν| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hpc0.le
    have h4 : pc * |lyap C i ν| ≤ pc * (B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hpc0.le
    have h5 : ρ ≤ M / 2 / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  · subst hν
    show 3 * ρ < (∑ j ∈ I, t * p j * lyap C j ν) - pc * lyap C i ν
    have hzero : ∑ j ∈ I, t * p j * lyap C j ν = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]
    have h1 : c ≤ -lyap C i ν := hc i hi
    have h2 : pc * c ≤ pc * (-lyap C i ν) := mul_le_mul_of_nonneg_left h1 hpc0.le
    have h5 : ρ ≤ pc * c / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hpcc : 0 < pc * c := mul_pos hpc0 hc0
    have h6 : pc * (-lyap C i ν) = -(pc * lyap C i ν) := mul_neg _ _
    rw [hzero]
    linarith

end StochKolmogorov.Extinct

namespace StochKolmogorov.Extinct
open EthierKurtz

/-- The reduction glue: (5.1)-(5.2) from face invariance, the TV overlap on face boxes (finiteness
of `subErgodic`) and the vanishing of the supported Lyapunov exponents (Classify Lemma 5.1). -/
theorem inequalities_glue {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ phat : Fin n → ℝ, (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀ ∧
      ∃ pcheck : ℝ, 0 < pcheck ∧ pcheck < δ₀ ∧
      ∃ ρe : ℝ, 0 < ρe ∧
        ∀ ν : Measure (SDEState n), (ν ∈ subErgodic P X mu ∨ ν = mu) →
          ∀ i : Fin n, i ∉ supp mu →
            3 * ρe < (∑ j ∈ supp mu, phat j * lyap C j ν) - pcheck * lyap C i ν := by
  obtain ⟨hPprob, hB, hsol⟩ := hX
  haveI := hPprob
  have hpd := hA.1
  have hC := hA.2.1
  let C' : Persist.Coeffs n := ⟨C.f, C.g, C.Γ⟩
  have hX' : Persist.IsSolutionFamily P C' B X := ⟨hPprob, hB, hsol⟩
  have hC' : ∀ i, LocallyLipschitzOn (Persist.orthant n) (C'.f i) ∧
      LocallyLipschitzOn (Persist.orthant n) (C'.g i) := hC
  have hpd' : ∀ x ∈ Persist.orthant n,
      (Matrix.of fun i j => C'.g i x * C'.g j x * C'.sig i j).PosDef := hpd
  have hfaceAE : ∀ (J : Finset (Fin n)) (x : SDEState n), x ∈ Persist.faceOpen J →
      ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ Persist.faceOpen J := fun J x hx =>
    Persist.kolmogorov_sde_face_invariance C' hB hC' hx (hsol x hx.1)
  have hface : ∀ (J : Finset (Fin n)) (x : SDEState n), x ∈ Persist.faceOpen J →
      ∀ t, trans P X t x (Persist.faceOpen J)ᶜ = 0 :=
    fun J x hx t => trans_compl_face_zero hfaceAE J x hx t
  have hovl : ∀ (J : Finset (Fin n)) (α β : ℝ), 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ Persist.faceOpen J, (∀ i ∈ J, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε :=
    fun J α β hα hαβ => Persist.kolmogorov_face_box_tv_overlap P C' B X hX' hC' hpd' J hα hαβ
  have hfin : (subErgodic P X mu).Finite := subErgodic_finite_of hface hovl mu
  let C'' : Classify.Coeffs n := ⟨C.f, C.g, C.Γ⟩
  have hX'' : Classify.IsSolutionFamily P C'' B X := ⟨hPprob, hB, hsol⟩
  have hA'' : Classify.Assumption11 C'' c γb := hA
  have hmu'' : mu ∈ Classify.bdryErgodic P X := h13.1
  have hz : ∀ j ∈ supp mu, lyap C j mu = 0 := fun j hj =>
    (Classify.lemma_5_1 hn P C'' B X hX'' c γb hA'' mu hmu'' j hj).2
  exact childD_minimax_assembly P C X mu h13 hfin hz δ₀ hδ₀.1

end StochKolmogorov.Extinct

open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ phat : Fin n → ℝ, (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀ ∧
      ∃ pcheck : ℝ, 0 < pcheck ∧ pcheck < δ₀ ∧
      ∃ ρe : ℝ, 0 < ρe ∧
        ∀ ν : Measure (SDEState n), (ν ∈ subErgodic P X mu ∨ ν = mu) →
          ∀ i : Fin n, i ∉ supp mu →
            3 * ρe < (∑ j ∈ supp mu, phat j * lyap C j ν) - pcheck * lyap C i ν := by
  exact inequalities_glue hn P C B X hX c γb hA mu h13 δ₀ hδ₀
