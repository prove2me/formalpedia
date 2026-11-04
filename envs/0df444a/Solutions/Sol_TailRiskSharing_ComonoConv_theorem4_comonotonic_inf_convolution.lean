-- Prove2me | solution 1 for TailRiskSharing.ComonoConv.theorem4_comonotonic_inf_convolution
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:49:31.705397+00:00
-- url     : https://prove2.me/submissions/2b156312-fbd0-4b11-a19a-8ca7619c2edf

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

set_option autoImplicit false

open MeasureTheory Set

namespace C4Disproof

/-- The cumulative function `c ↦ μ (s ∩ Iic c)` (as a real) for `μ = volume.restrict (Icc 0 1)`
is `1`-Lipschitz. -/
theorem A_lipschitz (s : Set ℝ) :
    LipschitzWith 1 (fun c : ℝ => ((volume.restrict (Icc (0:ℝ) 1)) (s ∩ Iic c)).toReal) := by
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμdef
  apply LipschitzWith.of_le_add
  intro x y
  have hfin : ∀ u : Set ℝ, μ u ≠ ⊤ := fun u => measure_ne_top μ u
  rcases le_total x y with hxy | hyx
  · have h1 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) :=
      measure_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.2 hxy))
    have h2 : (μ (s ∩ Iic x)).toReal ≤ (μ (s ∩ Iic y)).toReal :=
      ENNReal.toReal_mono (hfin _) h1
    have : 0 ≤ dist x y := dist_nonneg
    linarith
  · have hsub : s ∩ Iic x ⊆ (s ∩ Iic y) ∪ Ioc y x := by
      intro z hz
      by_cases hzy : z ≤ y
      · exact Or.inl ⟨hz.1, hzy⟩
      · exact Or.inr ⟨lt_of_not_ge hzy, hz.2⟩
    have h1 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) + μ (Ioc y x) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h3 : μ (Ioc y x) ≤ ENNReal.ofReal (x - y) := by
      calc μ (Ioc y x) ≤ volume (Ioc y x) := Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal (x - y) := Real.volume_Ioc
    have h4 : μ (s ∩ Iic x) ≤ μ (s ∩ Iic y) + ENNReal.ofReal (x - y) :=
      h1.trans (add_le_add le_rfl h3)
    have h5 : (μ (s ∩ Iic x)).toReal ≤ (μ (s ∩ Iic y) + ENNReal.ofReal (x - y)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, ENNReal.ofReal_ne_top⟩) h4
    rw [ENNReal.toReal_add (hfin _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (sub_nonneg.2 hyx)] at h5
    have : dist x y = x - y := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx)]
    linarith

/-- `volume.restrict (Icc 0 1)` is atomless in the classical sense. -/
theorem A_atomless_real :
    TailRiskSharing.ComonoConv.IsAtomless (volume.restrict (Icc (0:ℝ) 1)) := by
  set μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hμdef
  intro s hs hpos
  have hfin : ∀ u : Set ℝ, μ u ≠ ⊤ := fun u => measure_ne_top μ u
  set g : ℝ → ℝ := fun c => (μ (s ∩ Iic c)).toReal with hg
  have hcont : Continuous g := (A_lipschitz s).continuous
  have hg0 : g 0 = 0 := by
    have : μ (s ∩ Iic 0) = 0 := by
      rw [hμdef, Measure.restrict_apply (hs.inter measurableSet_Iic)]
      apply measure_mono_null (t := {0})
      · intro z hz
        simp only [mem_inter_iff, mem_Iic, mem_Icc] at hz
        simp only [mem_singleton_iff]
        linarith [hz.1.2, hz.2.1]
      · exact Real.volume_singleton
    simp [hg, this]
  have hg1 : g 1 = (μ s).toReal := by
    have : μ (s ∩ Iic 1) = μ s := by
      rw [hμdef, Measure.restrict_apply (hs.inter measurableSet_Iic), Measure.restrict_apply hs]
      congr 1
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.2⟩, h3⟩
    simp [hg, this]
  have hspos : 0 < (μ s).toReal := ENNReal.toReal_pos (ne_of_gt hpos) (hfin s)
  have hmem : (μ s).toReal / 2 ∈ Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    constructor <;> linarith
  obtain ⟨c, _, hc⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn hmem
  refine ⟨s ∩ Iic c, Set.inter_subset_left, hs.inter measurableSet_Iic, ?_, ?_⟩
  · have : 0 < (μ (s ∩ Iic c)).toReal := by
      have : g c = (μ (s ∩ Iic c)).toReal := rfl
      rw [← this, hc]; linarith
    exact ENNReal.toReal_pos_iff.1 this |>.1
  · rw [← ENNReal.toReal_lt_toReal (hfin _) (hfin _)]
    have : g c = (μ (s ∩ Iic c)).toReal := rfl
    rw [← this, hc]; linarith

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

lemma distFn_eq_cdf (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    (x : ℝ) : TailRiskSharing.VaRConv.distFn P Z x = ProbabilityTheory.cdf (P.map Z) x := by
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, Measure.map_apply hZ measurableSet_Iic]
  rfl

/-- Galois connection for the left quantile. -/
lemma varL_le_iff (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (x : ℝ) :
    TailRiskSharing.VaRConv.VaRL P α Z ≤ x ↔ 1 - α ≤ TailRiskSharing.VaRConv.distFn P Z x := by
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set F := ProbabilityTheory.cdf (P.map Z) with hF
  have hd : ∀ y, TailRiskSharing.VaRConv.distFn P Z y = F y := fun y => distFn_eq_cdf P Z hZ y
  simp only [TailRiskSharing.VaRConv.VaRL, hd]
  set S := {y | 1 - α ≤ F y} with hS
  have hne : S.Nonempty := by
    have := (ProbabilityTheory.tendsto_cdf_atTop (P.map Z)).eventually
      (Ioi_mem_nhds (show 1 - α < 1 by linarith))
    obtain ⟨y, hy⟩ := this.exists
    exact ⟨y, le_of_lt hy⟩
  have hbdd : BddBelow S := by
    have := (ProbabilityTheory.tendsto_cdf_atBot (P.map Z)).eventually
      (Iio_mem_nhds (show (0:ℝ) < 1 - α by linarith))
    obtain ⟨y0, hy0⟩ := Filter.eventually_atBot.1 this
    refine ⟨y0, fun y hy => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h2 := hy0 y hlt.le
    exact absurd hy (not_le.2 h2)
  have hmem : 1 - α ≤ F (sInf S) := by
    have hrc : ContinuousWithinAt F (Ioi (sInf S)) (sInf S) :=
      (F.right_continuous (sInf S)).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hrc
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hzS, hzy⟩ := (csInf_lt_iff hbdd hne).1 hy
    exact le_trans hzS (F.mono hzy.le)
  constructor
  · intro h; exact hmem.trans (F.mono h)
  · intro h; exact csInf_le hbdd h

lemma var_sum_nonneg (P : Measure Ω) [IsProbabilityMeasure P] (Z W : Ω → ℝ) (hZ : Measurable Z)
    (hW : Measurable W) (hZW : ∀ ω, Z ω + W ω = 0) :
    0 ≤ TailRiskSharing.VaRConv.VaRL P (3/10) Z + TailRiskSharing.VaRConv.VaRL P (3/10) W := by
  set a := TailRiskSharing.VaRConv.VaRL P (3/10) Z
  set b := TailRiskSharing.VaRConv.VaRL P (3/10) W
  have ha := (varL_le_iff P Z hZ (3/10) (by norm_num) (by norm_num) a).1 le_rfl
  have hb := (varL_le_iff P W hW (3/10) (by norm_num) (by norm_num) b).1 le_rfl
  by_contra hneg
  push_neg at hneg
  have hdisj : Disjoint {ω | Z ω ≤ a} {ω | W ω ≤ b} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [mem_setOf_eq] at h1 h2
    have := hZW ω
    linarith
  have hU := measureReal_union (μ := P) hdisj (measurableSet_le hW measurable_const)
  have hle : P.real ({ω | Z ω ≤ a} ∪ {ω | W ω ≤ b}) ≤ 1 := measureReal_le_one
  simp only [TailRiskSharing.VaRConv.distFn] at ha hb
  linarith

lemma varL_zero (P : Measure Ω) [IsProbabilityMeasure P] (α : ℝ) :
    TailRiskSharing.VaRConv.VaRL P α (fun _ => (0:ℝ)) = 0 := by
  have hd : ∀ x : ℝ, TailRiskSharing.VaRConv.distFn P (fun _ => (0:ℝ)) x =
      if 0 ≤ x then 1 else 0 := by
    intro x
    unfold TailRiskSharing.VaRConv.distFn
    split_ifs with h
    · simp [h]
    · simp [h]
  unfold TailRiskSharing.VaRConv.VaRL
  simp only [hd]
  rcases le_or_gt (1 - α) 0 with h | h
  · have : {x : ℝ | 1 - α ≤ if 0 ≤ x then (1:ℝ) else 0} = univ := by
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true]
      split_ifs <;> linarith
    rw [this, Real.sInf_univ]
  · rcases le_or_gt (1 - α) 1 with h' | h'
    · have : {x : ℝ | 1 - α ≤ if 0 ≤ x then (1:ℝ) else 0} = Ici 0 := by
        ext x
        simp only [mem_setOf_eq, mem_Ici]
        split_ifs with hx
        · exact ⟨fun _ => hx, fun _ => h'⟩
        · exact ⟨fun h2 => absurd h2 (not_le.2 h), fun h2 => absurd h2 hx⟩
      rw [this, csInf_Ici]
    · have : {x : ℝ | 1 - α ≤ if 0 ≤ x then (1:ℝ) else 0} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
        split_ifs <;> linarith
      rw [this, Real.sInf_empty]

/-- Lower bound of the uniform measure of a set containing an interval. -/
lemma unif_real_ge (s : Set ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hs : Icc a b ⊆ s) : b - a ≤ (volume.restrict (Icc (0:ℝ) 1)).real s := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine le_trans ?_ (measureReal_mono hs)
  rw [measureReal_def, Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.2 (Icc_subset_Icc ha hb), Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- Law of the tail `X_{1/2}` at the levels needed for the generator identity. -/
lemma tail_iff (P : Measure Ω) [IsProbabilityMeasure P] (X U : Ω → ℝ) (hX : Measurable X)
    (hU : Measurable U) (hmap : P.map U = volume.restrict (Icc (0:ℝ) 1)) (x : ℝ) :
    2/5 ≤ TailRiskSharing.VaRConv.distFn P (TailRiskSharing.ComonoConv.tailRV P (1/2) X U) x ↔
      7/10 ≤ TailRiskSharing.VaRConv.distFn P X x := by
  set F := TailRiskSharing.VaRConv.distFn P X x with hFdef
  have hae : ∀ᵐ ω ∂P, U ω ∈ Ico (0:ℝ) 1 := by
    have h1 : ∀ᵐ y ∂(P.map U), y ∈ Ico (0:ℝ) 1 := by
      rw [hmap]
      have hI : ∀ᵐ y ∂(volume.restrict (Icc (0:ℝ) 1)), y ∈ Icc (0:ℝ) 1 :=
        ae_restrict_mem measurableSet_Icc
      have hne : ∀ᵐ y ∂(volume.restrict (Icc (0:ℝ) 1)), y ≠ 1 := by
        apply ae_restrict_of_ae
        rw [ae_iff]
        simp
      filter_upwards [hI, hne] with y hy1 hy2
      exact ⟨hy1.1, lt_of_le_of_ne hy1.2 hy2⟩
    exact ae_of_ae_map hU.aemeasurable h1
  have hset : {ω | TailRiskSharing.ComonoConv.tailRV P (1/2) X U ω ≤ x} =ᵐ[P]
      {ω | U ω ≤ 2 * F - 1} := by
    apply Filter.eventuallyEq_set.2
    filter_upwards [hae] with ω hω
    simp only [mem_setOf_eq, TailRiskSharing.ComonoConv.tailRV]
    rw [varL_le_iff P X hX _ (by nlinarith [hω.2]) (by nlinarith [hω.1])]
    constructor <;> intro h <;> linarith
  have hreal : TailRiskSharing.VaRConv.distFn P (TailRiskSharing.ComonoConv.tailRV P (1/2) X U) x
      = (volume.restrict (Icc (0:ℝ) 1)).real (Iic (2 * F - 1)) := by
    unfold TailRiskSharing.VaRConv.distFn
    rw [measureReal_congr hset, ← hmap, measureReal_def, measureReal_def,
      Measure.map_apply hU measurableSet_Iic]
    rfl
  rw [hreal]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hle : (volume.restrict (Icc (0:ℝ) 1)).real (Iic (2 * F - 1)) ≤ max (2 * F - 1) 0 := by
      rw [measureReal_def, Measure.restrict_apply measurableSet_Iic]
      have hsub : Iic (2 * F - 1) ∩ Icc 0 1 ⊆ Icc 0 (max (2 * F - 1) 0) :=
        fun y hy => ⟨hy.2.1, le_max_of_le_left hy.1⟩
      have h2 := measure_mono (μ := volume) hsub
      rw [Real.volume_Icc] at h2
      have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      rw [ENNReal.toReal_ofReal (by simp)] at h3; simpa using h3
    have : max (2 * F - 1) 0 < 2/5 := max_lt (by linarith) (by norm_num)
    linarith
  · intro h
    have := unif_real_ge (Iic (2 * F - 1)) 0 (2/5) le_rfl (by norm_num) (by norm_num)
      (fun y hy => by simp only [mem_Iic]; linarith [hy.2])
    linarith

end Generic

end C4Disproof

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.ComonoConv.IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (ρ ρstar : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ)
    (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.ComonoConv.IsTailRiskMeasure P TailRiskSharing.ComonoConv.L0
      (εs i) (ρ i))
    (hgen : ∀ i, TailRiskSharing.ComonoConv.IsGenerator P TailRiskSharing.ComonoConv.L0
      (⨆ j, εs j) (ρ i) (ρstar i)),
    (∀ X ∈ TailRiskSharing.ComonoConv.L0, ∀ U : Ω → ℝ,
        TailRiskSharing.ComonoConv.IsQuantileUniform P X U →
        TailRiskSharing.ComonoConv.comonoInfConv P TailRiskSharing.ComonoConv.L0 ρ X =
          TailRiskSharing.ComonoConv.comonoInfConv P TailRiskSharing.ComonoConv.L0 ρstar
            (TailRiskSharing.ComonoConv.tailRV P (⨆ j, εs j) X U)) ∧
      TailRiskSharing.VaRTail.IsTailRiskMeasureE P TailRiskSharing.ComonoConv.L0 (⨆ j, εs j)
        (TailRiskSharing.ComonoConv.comonoInfConv P TailRiskSharing.ComonoConv.L0 ρ)) := by
  intro h
  set P : Measure ℝ := volume.restrict (Icc (0:ℝ) 1) with hPdef
  haveI hprob : IsProbabilityMeasure P := by
    constructor
    rw [hPdef, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  have hsup : (⨆ _j : Fin 2, (1/2:ℝ)) = 1/2 := ciSup_const
  have htail : ∀ i : Fin 2, TailRiskSharing.ComonoConv.IsTailRiskMeasure P
      TailRiskSharing.ComonoConv.L0 ((fun _ => (1/2:ℝ)) i)
      ((fun _ => TailRiskSharing.VaRConv.VaRL P (3/10)) i) := by
    intro i X _ Y _ hXY
    simp only
    unfold TailRiskSharing.VaRConv.VaRL
    congr 1
    ext x
    simp only [mem_setOf_eq]
    have key : ∀ a : ℝ, (1 - 3/10 ≤ a ↔ 1/5 ≤ max (a - (1 - 1/2)) 0) := by
      intro a
      constructor
      · intro ha; exact le_max_of_le_left (by linarith)
      · intro ha
        rcases le_max_iff.1 ha with h | h
        · linarith
        · norm_num at h
    have hx := hXY x
    simp only [TailRiskSharing.ComonoConv.distFn] at hx
    simp only [TailRiskSharing.VaRConv.distFn]
    rw [key, key, hx]
  have hgen : ∀ i : Fin 2, TailRiskSharing.ComonoConv.IsGenerator P
      TailRiskSharing.ComonoConv.L0 (⨆ _j : Fin 2, (1/2:ℝ))
      ((fun _ => TailRiskSharing.VaRConv.VaRL P (3/10)) i)
      ((fun _ => TailRiskSharing.VaRConv.VaRL P (3/5)) i) := by
    intro i
    rw [hsup]
    refine ⟨?_, ?_⟩
    · intro X _ Y _ hXY
      simp only [TailRiskSharing.VaRConv.VaRL, hXY]
    · intro X hX U hU
      simp only
      unfold TailRiskSharing.VaRConv.VaRL
      congr 1
      ext x
      simp only [mem_setOf_eq]
      rw [show (1:ℝ) - 3/5 = 2/5 by norm_num, show (1:ℝ) - 3/10 = 7/10 by norm_num]
      exact (C4Disproof.tail_iff P X U hX hU.1 hU.2.1 x).symm
  have hQU : TailRiskSharing.ComonoConv.IsQuantileUniform P (fun _ => (0:ℝ)) id := by
    refine ⟨measurable_id, Measure.map_id, ae_of_all _ (fun ω => ?_)⟩
    exact C4Disproof.varL_zero P _
  have hE := (h (Ω := ℝ) P C4Disproof.A_atomless_real 2 (by norm_num)
    (fun _ => TailRiskSharing.VaRConv.VaRL P (3/10))
    (fun _ => TailRiskSharing.VaRConv.VaRL P (3/5)) (fun _ => 1/2)
    (fun _ => ⟨by norm_num, by norm_num⟩) htail hgen).1 (fun _ => 0) measurable_const id hQU
  have htz : ∀ e : ℝ, TailRiskSharing.ComonoConv.tailRV P e (fun _ => (0:ℝ)) id = fun _ => 0 :=
    fun e => funext fun ω => C4Disproof.varL_zero P _
  rw [htz] at hE
  have hL : ((0:ℝ) : EReal) ≤ TailRiskSharing.ComonoConv.comonoInfConv P
      TailRiskSharing.ComonoConv.L0 (fun _ : Fin 2 => TailRiskSharing.VaRConv.VaRL P (3/10))
      (fun _ => 0) := by
    unfold TailRiskSharing.ComonoConv.comonoInfConv
    refine le_iInf₂ fun Xs hXs => ?_
    obtain ⟨⟨hmeas, hsum⟩, _⟩ := hXs
    have := C4Disproof.var_sum_nonneg P (Xs 0) (Xs 1) (hmeas 0) (hmeas 1)
      (fun ω => by simpa [Fin.sum_univ_two] using hsum ω)
    rw [Fin.sum_univ_two]
    exact_mod_cast this
  set Z : ℝ → ℝ := fun ω => if ω ≤ 2/5 then -1 else 1 with hZ
  have hZm : Measurable Z := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have h1 : TailRiskSharing.VaRConv.VaRL P (3/5) Z ≤ -1 := by
    rw [C4Disproof.varL_le_iff P Z hZm _ (by norm_num) (by norm_num)]
    have := C4Disproof.unif_real_ge {ω | Z ω ≤ -1} 0 (2/5) le_rfl (by norm_num) (by norm_num)
      (fun y hy => by simp only [mem_setOf_eq, hZ, if_pos hy.2]; rfl)
    unfold TailRiskSharing.VaRConv.distFn
    linarith
  have h2 : TailRiskSharing.VaRConv.VaRL P (3/5) (fun ω => - Z ω) ≤ -1 := by
    rw [C4Disproof.varL_le_iff P (fun ω => - Z ω) hZm.neg _ (by norm_num) (by norm_num)]
    have := C4Disproof.unif_real_ge {ω | - Z ω ≤ -1} (1/2) 1 (by norm_num) (by norm_num) le_rfl
      (fun y hy => by
        have : ¬ y ≤ 2/5 := by linarith [hy.1]
        simp only [mem_setOf_eq, hZ, if_neg this]; rfl)
    unfold TailRiskSharing.VaRConv.distFn
    linarith
  have hR : TailRiskSharing.ComonoConv.comonoInfConv P TailRiskSharing.ComonoConv.L0
      (fun _ : Fin 2 => TailRiskSharing.VaRConv.VaRL P (3/5)) (fun _ => 0) ≤ ((-2 : ℝ) : EReal) := by
    unfold TailRiskSharing.ComonoConv.comonoInfConv
    refine (iInf₂_le (![Z, fun ω => - Z ω]) ?_).trans ?_
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        fin_cases i
        · exact hZm
        · exact hZm.neg
      · intro ω
        simp [Fin.sum_univ_two]
      · intro i
        exact ⟨univ, MeasurableSet.univ, measure_univ, fun _ _ _ _ => by simp⟩
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact_mod_cast (by linarith : TailRiskSharing.VaRConv.VaRL P (3/5) Z +
        TailRiskSharing.VaRConv.VaRL P (3/5) (fun ω => - Z ω) ≤ -2)
  rw [hE] at hL
  have := EReal.coe_le_coe_iff.1 (hL.trans hR)
  norm_num at this
