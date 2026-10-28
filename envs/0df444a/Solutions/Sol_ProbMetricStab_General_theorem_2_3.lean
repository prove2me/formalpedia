-- Prove2me | solution 1 for ProbMetricStab.General.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T09:26:23.98042+00:00
-- url     : https://prove2.me/submissions/eff09510-f87c-494d-8255-5cbe24923f51

import Definitions.Def_ProbMetricStab_General_Setting
import Mathlib


open MeasureTheory
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
open DupacovaWets.Consistency
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f g : Ω → EReal}

theorem expect_mono (hfg : ∀ ω, f ω ≤ g ω) : expect ν f ≤ expect ν g := by
  have hp : (∫⁻ ω, (f ω).toENNReal ∂ν) ≤ ∫⁻ ω, (g ω).toENNReal ∂ν :=
    lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (hfg ω)
  have hn : (∫⁻ ω, (-g ω).toENNReal ∂ν) ≤ ∫⁻ ω, (-f ω).toENNReal ∂ν :=
    lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfg ω))
  unfold expect
  split_ifs with hf hg hg
  · rfl
  · exact False.elim (hg (top_unique (hf ▸ hp)))
  · exact le_top
  · exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hp)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hn)

theorem expect_pos_finite (h : expect ν f < ⊤) :
    (∫⁻ ω, (f ω).toENNReal ∂ν) ≠ ⊤ := by
  intro hf
  simp [expect, hf] at h

theorem expect_neg_finite (hp : (∫⁻ ω, (f ω).toENNReal ∂ν) ≠ ⊤)
    (h : ⊥ < expect ν f) : (∫⁻ ω, (-f ω).toENNReal ∂ν) ≠ ⊤ := by
  intro hn
  simp [expect, hp, hn] at h

theorem expect_eq_real_parts
    (hp : (∫⁻ ω, (f ω).toENNReal ∂ν) ≠ ⊤)
    (hn : (∫⁻ ω, (-f ω).toENNReal ∂ν) ≠ ⊤) :
    expect ν f = (((∫⁻ ω, (f ω).toENNReal ∂ν).toReal -
      (∫⁻ ω, (-f ω).toENNReal ∂ν).toReal : ℝ) : EReal) := by
  rw [expect, if_neg hp, EReal.coe_sub]
  rw [EReal.coe_ennreal_toReal hp, EReal.coe_ennreal_toReal hn]

theorem expect_finite_of_parts
    (hp : (∫⁻ ω, (f ω).toENNReal ∂ν) ≠ ⊤)
    (hn : (∫⁻ ω, (-f ω).toENNReal ∂ν) ≠ ⊤) :
    expect ν f ≠ ⊤ ∧ expect ν f ≠ ⊥ := by
  rw [expect_eq_real_parts hp hn]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
end ProbMetricStab.General.PMSFresh

open MeasureTheory
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh

theorem shift_parts (z : EReal) (b : ℝ) (hb : 0 ≤ b)
    (hz : (-z).toENNReal ≤ ENNReal.ofReal b) :
    (z + (b : EReal)).toENNReal + (-z).toENNReal =
      z.toENNReal + ENNReal.ofReal b := by
  induction z using EReal.rec with
  | bot => simp at hz
  | top => simp
  | coe z =>
    have hzb : -z ≤ b := by
      rw [← EReal.coe_neg, EReal.real_coe_toENNReal] at hz
      exact (ENNReal.ofReal_le_ofReal_iff hb).mp hz
    rw [← EReal.coe_add, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    by_cases hz0 : 0 ≤ z
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hz0), add_zero,
        ENNReal.ofReal_add hz0 hb]
    · have hz0' : z ≤ 0 := le_of_not_ge hz0
      rw [ENNReal.ofReal_of_nonpos hz0', zero_add,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ z+b) (neg_nonneg.mpr hz0')]
      congr 1
      ring

theorem parts_balance (A P N B : ℝ≥0∞) (hN : N ≠ ∞) (hB : B ≠ ∞)
    (he : A + N = P + B) :
    (if P = ∞ then (⊤ : EReal) else (P : EReal) - (N : EReal)) =
      (A : EReal) - (B : EReal) := by
  by_cases hP : P = ∞
  · have hA : A = ∞ := by
      have : A + N = ∞ := by simpa [hP] using he
      simpa [hN] using this
    simp only [hP, hA, EReal.coe_ennreal_top]
    exact (EReal.top_sub (EReal.coe_ennreal_eq_top_iff.not.mpr hB)).symm
  · have hA : A ≠ ∞ := by
      intro ha
      have : P + B = ∞ := by simpa [ha] using he.symm
      simp [hP, hB] at this
    have her : A.toReal + N.toReal = P.toReal + B.toReal := by
      simpa only [ENNReal.toReal_add hA hN, ENNReal.toReal_add hP hB] using congrArg ENNReal.toReal he
    rw [if_neg hP, ← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hN,
      ← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith
end ProbMetricStab.General.PMSFresh

open MeasureTheory Filter
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
open DupacovaWets.Consistency
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem expect_shift {f : Ω → EReal} (hf : Measurable f) {b : Ω → ℝ}
    (hb : Measurable b) (hb0 : ∀ ω, 0 ≤ b ω)
    (hbi : (∫⁻ ω, ENNReal.ofReal (b ω) ∂ν) ≠ ∞)
    (hlow : ∀ᵐ ω ∂ν, (-f ω).toENNReal ≤ ENNReal.ofReal (b ω)) :
    expect ν f = ((∫⁻ ω, (f ω + (b ω : EReal)).toENNReal ∂ν : ℝ≥0∞) : EReal) -
      ((∫⁻ ω, ENNReal.ofReal (b ω) ∂ν : ℝ≥0∞) : EReal) := by
  have hn : (∫⁻ ω, (-f ω).toENNReal ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top hbi (lintegral_mono_ae hlow)
  have hbalance : (∫⁻ ω, (f ω + (b ω : EReal)).toENNReal ∂ν) +
      (∫⁻ ω, (-f ω).toENNReal ∂ν) =
      (∫⁻ ω, (f ω).toENNReal ∂ν) + (∫⁻ ω, ENNReal.ofReal (b ω) ∂ν) := by
    have hm : Measurable (fun ω => (f ω + (b ω : EReal)).toENNReal) :=
      (hf.add hb.coe_real_ereal).ereal_toENNReal
    rw [← lintegral_add_left hm,
      ← lintegral_add_left hf.ereal_toENNReal]
    apply lintegral_congr_ae
    filter_upwards [hlow] with ω hω
    exact shift_parts (f ω) (b ω) (hb0 ω) hω
  exact parts_balance _ _ _ _ hn hbi hbalance
end ProbMetricStab.General.PMSFresh

open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh

theorem lintegral_lsc {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [SequentialSpace E] (ν : Measure Ω) (f : E → Ω → ℝ≥0∞)
    (hf : ∀ x, Measurable (f x)) (hls : ∀ ω, LowerSemicontinuous (fun x => f x ω)) :
    LowerSemicontinuous (fun x => ∫⁻ ω, f x ω ∂ν) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  apply IsSeqClosed.isClosed
  intro x z hx hz
  change (∫⁻ ω, f z ω ∂ν) ≤ r
  calc
    _ ≤ ∫⁻ ω, liminf (fun n => f (x n) ω) atTop ∂ν := by
      apply lintegral_mono
      intro ω
      exact (LowerSemicontinuousAt.le_liminf (hls ω z)).trans hz.liminf_le_liminf_comp
    _ ≤ liminf (fun n => ∫⁻ ω, f (x n) ω ∂ν) atTop :=
      lintegral_liminf_le fun n => hf (x n)
    _ ≤ r := liminf_le_of_frequently_le' (Filter.Eventually.of_forall hx).frequently

theorem shifted_lsc {E : Type*} [TopologicalSpace E] {f : E → EReal}
    (hf : LowerSemicontinuous f) (b : ℝ) :
    LowerSemicontinuous (fun x => (f x + (b : EReal)).toENNReal) := by
  have ha : LowerSemicontinuous (fun x => f x + (b : EReal)) :=
    hf.add' continuous_const.lowerSemicontinuous fun x =>
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot b)) (Or.inr (EReal.coe_ne_top b))
  exact EReal.continuous_toENNReal.comp_lowerSemicontinuous ha
    (fun _ _ h => EReal.toENNReal_le_toENNReal h)
end ProbMetricStab.General.PMSFresh

open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
open DupacovaWets.Consistency

theorem expect_lsc_of_lower_bound {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [SequentialSpace E] (ν : Measure Ω) (f : E → Ω → EReal)
    (hf : ∀ x, Measurable (f x)) (hls : ∀ ω, LowerSemicontinuous (fun x => f x ω))
    (b : Ω → ℝ) (hb : Measurable b) (hb0 : ∀ ω, 0 ≤ b ω)
    (hbi : (∫⁻ ω, ENNReal.ofReal (b ω) ∂ν) ≠ ∞)
    (hlow : ∀ x, ∀ᵐ ω ∂ν, (-f x ω).toENNReal ≤ ENNReal.ofReal (b ω)) :
    LowerSemicontinuous (fun x => expect ν (f x)) := by
  let B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (b ω) ∂ν
  let A : E → ℝ≥0∞ := fun x => ∫⁻ ω, (f x ω + (b ω : EReal)).toENNReal ∂ν
  have hA : LowerSemicontinuous A := lintegral_lsc ν _
    (fun x => ((hf x).add hb.coe_real_ereal).ereal_toENNReal)
    (fun ω => shifted_lsc (hls ω) (b ω))
  have hcont : Continuous (fun a : ℝ≥0∞ => (a : EReal) + ((-B.toReal : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))).comp
      (continuous_coe_ennreal_ereal.continuousAt.prodMk continuous_const.continuousAt)
  have hmono : Monotone (fun a : ℝ≥0∞ => (a : EReal) + ((-B.toReal : ℝ) : EReal)) := by
    intro a c hac
    exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hac) le_rfl
  have h := hcont.comp_lowerSemicontinuous hA hmono
  have he : (fun x => expect ν (f x)) =
      (fun a : ℝ≥0∞ => (a : EReal) + ((-B.toReal : ℝ) : EReal)) ∘ A := by
    funext x
    rw [expect_shift (hf x) hb hb0 hbi (hlow x)]
    dsimp only [Function.comp_def, A]
    rw [EReal.coe_neg, ← EReal.coe_ennreal_toReal hbi]
    rfl
  rwa [he]
end ProbMetricStab.General.PMSFresh

open Set Metric MeasureTheory
namespace ProbMetricStab.General.PMSFresh

 theorem compact_hit_iff {E : Type*} [PseudoMetricSpace E] {F K : Set E}
    (hF : IsClosed F) (hK : IsCompact K) :
    (F ∩ K).Nonempty ↔ ∀ n : ℕ, (F ∩ thickening (1 / ((n : ℝ) + 1)) K).Nonempty := by
  constructor
  · rintro ⟨x, hx, hxK⟩ n
    exact ⟨x, hx, self_subset_thickening (by positivity) K hxK⟩
  · intro h
    by_contra hn
    have hsub : K ⊆ Fᶜ := by
      intro x hx hxf
      exact hn ⟨x, hxf, hx⟩
    obtain ⟨δ, hδ, hs⟩ := hK.exists_thickening_subset_open hF.isOpen_compl hsub
    obtain ⟨n, hnδ⟩ := exists_nat_one_div_lt hδ
    obtain ⟨x, hxF, hxK⟩ := h n
    exact hs (thickening_mono hnδ.le K hxK) hxF

 theorem measurable_compact_hit {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (F : Ω → Set E) (hclosed : ∀ ω, IsClosed (F ω))
    (hopen : ∀ O : Set E, IsOpen O → MeasurableSet {ω | (F ω ∩ O).Nonempty})
    {K : Set E} (hK : IsCompact K) : MeasurableSet {ω | (F ω ∩ K).Nonempty} := by
  have he : {ω | (F ω ∩ K).Nonempty} =
      ⋂ n : ℕ, {ω | (F ω ∩ thickening (1 / ((n : ℝ) + 1)) K).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact compact_hit_iff (hclosed ω) hK
  rw [he]
  exact MeasurableSet.iInter fun n => hopen _ isOpen_thickening
end ProbMetricStab.General.PMSFresh

open Set MeasureTheory
namespace ProbMetricStab.General.PMSFresh

theorem ereal_bot_level {Ω : Type*} (f : Ω → EReal) :
    {ω | f ω ≤ ⊥} = ⋂ n : ℕ, {ω | f ω ≤ ((-(n : ℝ)) : EReal)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter]
  constructor
  · intro h n
    exact h.trans bot_le
  · intro h
    by_contra hn
    obtain ⟨r, _, hr⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    obtain ⟨n, hn⟩ := exists_nat_gt (-r)
    have hnr : (-(n : ℝ)) < r := by linarith
    exact (not_le_of_gt ((EReal.coe_lt_coe_iff.mpr hnr).trans hr)) (h n)

theorem measurable_ereal_of_real_levels {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → EReal) (hf : ∀ r : ℝ, MeasurableSet {ω | f ω ≤ (r : EReal)}) :
    Measurable f := by
  apply measurable_of_Iic
  intro r
  induction r using EReal.rec with
  | bot =>
    change MeasurableSet {ω | f ω ≤ ⊥}
    rw [ereal_bot_level]
    exact MeasurableSet.iInter fun n => hf _
  | coe r => exact hf r
  | top => simp

theorem lsc_ereal_of_real_levels {E : Type*} [TopologicalSpace E]
    (f : E → EReal) (hf : ∀ r : ℝ, IsClosed {x | f x ≤ (r : EReal)}) :
    LowerSemicontinuous f := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  induction r using EReal.rec with
  | bot =>
    change IsClosed {x | f x ≤ ⊥}
    rw [ereal_bot_level]
    exact isClosed_iInter fun n => hf _
  | coe r => exact hf r
  | top => simp
end ProbMetricStab.General.PMSFresh

open Set Metric MeasureTheory
namespace ProbMetricStab.General.PMSFresh
variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → EuclideanSpace ℝ (Fin m) → EReal}

theorem normal_lsc (hg : IsNormalIntegrand g) (ω : Ω) : LowerSemicontinuous (g ω) := by
  apply lsc_ereal_of_real_levels
  intro r
  exact (hg.1 ω).preimage (continuous_id.prodMk continuous_const)

theorem normal_measurable (hg : IsNormalIntegrand g) (x : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun ω => g ω x) := by
  apply measurable_ereal_of_real_levels
  intro r
  have h := measurable_compact_hit _ hg.1 hg.2 (isCompact_singleton (x := (x, r)))
  simpa only [inter_singleton_nonempty, mem_ofPred_eq] using h

theorem normal_inf_attained (hg : IsNormalIntegrand g)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (hne : K.Nonempty) (ω : Ω) :
    ∃ x ∈ K, (⨅ y ∈ K, g ω y) = g ω x := by
  obtain ⟨x, hx, hm⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK ((normal_lsc hg ω).lowerSemicontinuousOn K)
  refine ⟨x, hx, le_antisymm (iInf_le_of_le x (iInf_le _ hx)) ?_⟩
  exact le_iInf fun y => le_iInf fun hy => hm hy

theorem normal_inf_measurable (hg : IsNormalIntegrand g)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) :
    Measurable (fun ω => ⨅ x ∈ K, g ω x) := by
  by_cases hne : K.Nonempty
  · apply measurable_ereal_of_real_levels
    intro r
    have h := measurable_compact_hit _ hg.1 hg.2 (hK.prod (isCompact_singleton (x := r)))
    have he : {ω | (⨅ x ∈ K, g ω x) ≤ (r : EReal)} =
        {ω | ({p : EuclideanSpace ℝ (Fin m) × ℝ | g ω p.1 ≤ (p.2 : EReal)} ∩
          K ×ˢ {r}).Nonempty} := by
      ext ω
      constructor
      · intro hw
        change (⨅ x ∈ K, g ω x) ≤ (r : EReal) at hw
        obtain ⟨x, hx, hmin⟩ := normal_inf_attained hg hK hne ω
        refine ⟨(x, r), ?_, hx, rfl⟩
        change g ω x ≤ (r : EReal)
        rwa [hmin] at hw
      · rintro ⟨⟨x, t⟩, hx, hxK, ht⟩
        have ht' : t = r := ht
        subst t
        change g ω x ≤ (r : EReal) at hx
        change (⨅ y ∈ K, g ω y) ≤ (r : EReal)
        exact (iInf_le_of_le x (iInf_le _ hxK)).trans hx
    rw [he]
    exact h
  · have hKe : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [hKe, mem_empty_iff_false, iInf_of_empty, iInf_const]
    exact measurable_const
end ProbMetricStab.General.PMSFresh

open MeasureTheory Set
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {ν : Measure ↥P.Ξ}

theorem integral_lt_top (hν : ν ∈ P.PFU U) (j : Fin (d+1))
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ P.X ∩ closure U) :
    P.integral ν j x < ⊤ := by
  apply lt_of_le_of_lt _ (hν.2 j).2
  exact le_iSup_of_le x (le_iSup (fun _ : x ∈ P.X ∩ closure U => P.integral ν j x) hx)

theorem integral_gt_bot (hν : ν ∈ P.PFU U) (j : Fin (d+1))
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ P.X) :
    ⊥ < P.integral ν j x := by
  have h := (hν.2 j).1 (‖x‖+1) (by positivity)
  apply h.trans_le
  apply expect_mono
  intro ω
  exact iInf_le_of_le x (iInf_le _ ⟨hx, by linarith⟩)

theorem integral_finite (hν : ν ∈ P.PFU U) (j : Fin (d+1))
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ P.X ∩ closure U) :
    P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥ :=
  ⟨(integral_lt_top hν j hx).ne, (integral_gt_bot hν j hx.1).ne'⟩

theorem envelope_parts_finite (hν : ν ∈ P.PFU U) (j : Fin (d+1))
    {x₀ : EuclideanSpace ℝ (Fin m)} (hx₀ : x₀ ∈ P.X ∩ closure U)
    {r : ℝ} (hr : 0 < r) (hxr : ‖x₀‖ ≤ r) :
    (∫⁻ ω, (⨅ x ∈ {x | x ∈ P.X ∧ ‖x‖ ≤ r}, P.f j ω x).toENNReal ∂ν) ≠ ∞ ∧
    (∫⁻ ω, (-(⨅ x ∈ {x | x ∈ P.X ∧ ‖x‖ ≤ r}, P.f j ω x)).toENNReal ∂ν) ≠ ∞ := by
  have he : DupacovaWets.Consistency.expect ν
      (fun ω => ⨅ x ∈ {x | x ∈ P.X ∧ ‖x‖ ≤ r}, P.f j ω x) < ⊤ := by
    apply lt_of_le_of_lt _ (integral_lt_top hν j hx₀)
    apply expect_mono
    intro ω
    exact iInf_le_of_le x₀ (iInf_le _ ⟨hx₀.1, hxr⟩)
  have hp := expect_pos_finite he
  exact ⟨hp, expect_neg_finite hp ((hν.2 j).1 r hr)⟩
end ProbMetricStab.General.PMSFresh

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {ν : Measure ↥P.Ξ}

theorem integral_lsc_on_ball (hg : P.GeneralAssumptions) (hν : ν ∈ P.PFU U)
    (j : Fin (d+1)) {x₀ : EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ P.X ∩ closure U) {r : ℝ} (hr : 0 < r) (hxr : ‖x₀‖ ≤ r) :
    LowerSemicontinuousOn (P.integral ν j) {x | x ∈ P.X ∧ ‖x‖ ≤ r} := by
  let K : Set (EuclideanSpace ℝ (Fin m)) := {x | x ∈ P.X ∧ ‖x‖ ≤ r}
  have hK : IsCompact K := by
    have he : K = P.X ∩ closedBall 0 r := by ext x; simp [K, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) r).inter_left hg.X_closed
  let g : ↥P.Ξ → EReal := fun ω => ⨅ x ∈ K, P.f j ω x
  have hgm : Measurable g := normal_inf_measurable (hg.normal j) hK
  have hN : (∫⁻ ω, (-g ω).toENNReal ∂ν) ≠ ∞ :=
    (envelope_parts_finite hν j hx₀ hr hxr).2
  let b : ↥P.Ξ → ℝ := fun ω => (-g ω).toENNReal.toReal
  have hbm : Measurable b := hgm.neg.ereal_toENNReal.ennreal_toReal
  have hb0 : ∀ ω, 0 ≤ b ω := fun _ => ENNReal.toReal_nonneg
  have hbi : (∫⁻ ω, ENNReal.ofReal (b ω) ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top hN (lintegral_mono fun ω => ENNReal.ofReal_toReal_le)
  have hbnd : ∀ x : K, ∀ᵐ ω ∂ν,
      (-(P.f j ω x)).toENNReal ≤ ENNReal.ofReal (b ω) := by
    intro x
    filter_upwards [ae_lt_top hgm.neg.ereal_toENNReal hN] with ω hω
    change (-(P.f j ω x)).toENNReal ≤ ENNReal.ofReal ((-g ω).toENNReal.toReal)
    change (-g ω).toENNReal < ∞ at hω
    rw [ENNReal.ofReal_toReal hω.ne]
    apply EReal.toENNReal_le_toENNReal
    apply EReal.neg_le_neg_iff.mpr
    exact iInf_le_of_le x.val (iInf_le _ x.property)
  apply lowerSemicontinuous_restrict_iff.mp
  exact expect_lsc_of_lower_bound ν (fun x : K => fun ω => P.f j ω x)
    (fun x => normal_measurable (hg.normal j) x)
    (fun ω => Semicontinuous.comp (normal_lsc (hg.normal j) ω) continuous_subtype_val)
    b hbm hb0 hbi hbnd
end ProbMetricStab.General.PMSFresh

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSFresh
variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {ν : Measure ↥P.Ξ}

theorem integral_lsc (hg : P.GeneralAssumptions) (hν : ν ∈ P.PFU U)
    (hKne : (P.X ∩ closure U).Nonempty) (j : Fin (d+1)) :
    LowerSemicontinuousOn (P.integral ν j) P.X := by
  obtain ⟨x₀, hx₀⟩ := hKne
  intro x hx
  let r : ℝ := ‖x‖ + ‖x₀‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hxr : ‖x₀‖ ≤ r := by dsimp [r]; nlinarith [norm_nonneg x]
  have hxx : ‖x‖ < r := by dsimp [r]; nlinarith [norm_nonneg x₀]
  have hb := integral_lsc_on_ball hg hν j hx₀ hr hxr x ⟨hx, hxx.le⟩
  have he : {y | y ∈ P.X ∧ ‖y‖ ≤ r} = P.X ∩ closedBall 0 r := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right]
  have hn : closedBall (0 : EuclideanSpace ℝ (Fin m)) r ∈ 𝓝[P.X] x :=
    mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hxx)) ball_subset_closedBall)
  intro c hc
  have ht := hb c hc
  rw [he, nhdsWithin_inter_of_mem' hn] at ht
  exact ht
end ProbMetricStab.General.PMSFresh


open Set Metric
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

theorem exists_near_of_infEDist_le {E : Type*} [MetricSpace E] [ProperSpace E]
    {S : Set E} (hS : IsClosed S) (x : E) {r : ℝ} (hr : 0 ≤ r)
    (h : infEDist x S ≤ ENNReal.ofReal r) : ∃ y ∈ S, dist x y ≤ r := by
  have hne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, infEDist_empty] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  obtain ⟨y, hy, he⟩ := hS.exists_infDist_eq_dist hne x
  refine ⟨y, hy, ?_⟩
  rw [← he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hr)

theorem closed_sublevel_on {E : Type*} [TopologicalSpace E] {S : Set E}
    (hS : IsClosed S) {f : E → EReal} (hf : LowerSemicontinuousOn f S) (r : EReal) :
    IsClosed {x | x ∈ S ∧ f x ≤ r} := by
  have hr : LowerSemicontinuous (S.domRestrict f) := lowerSemicontinuous_restrict_iff.mpr hf
  have hc := hS.isClosedEmbedding_subtypeVal.isClosedMap _ (hr.isClosed_preimage r)
  convert hc using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Set.mem_Iic]
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {ν : Measure ↥P.Ξ}

theorem my_closed (hX : IsClosed P.X)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X) (y : Fin d → ℝ) :
    IsClosed (P.My ν y) := by
  have he : P.My ν y = P.X ∩ ⋂ i : Fin d, {x | x ∈ P.X ∧ P.integral ν i.succ x ≤ (y i : EReal)} := by
    ext x
    simp only [Model.My, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro hx
      exact ⟨hx.1, fun i => ⟨hx.1, hx.2 i⟩⟩
    · intro hx
      exact ⟨hx.1, fun i => (hx.2 i).2⟩
  rw [he]
  exact hX.inter (isClosed_iInter (fun i => closed_sublevel_on hX (hls i.succ) _))

theorem mu_eq_my_inter : P.MU U ν = P.My ν 0 ∩ closure U := by
  ext x
  simp only [Model.MU, Model.My, mem_ofPred_eq, mem_inter_iff, Pi.zero_apply, EReal.coe_zero]
  tauto

theorem mu_compact (hX : IsClosed P.X) (hUb : Bornology.IsBounded U)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X) :
    IsCompact (P.MU U ν) := by
  rw [mu_eq_my_inter]
  exact hUb.isCompact_closure.inter_left (my_closed hX hls 0)

theorem mu_subset_K : P.MU U ν ⊆ P.X ∩ closure U := fun _ h => h.1

theorem mu_subset_M : P.MU U ν ⊆ P.M ν := fun _ h => ⟨h.1.1, h.2⟩

theorem vu_eq_of_min {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ P.MU U ν)
    (hmin : IsMinOn (P.integral ν 0) (P.MU U ν) x) : P.vU U ν = P.integral ν 0 x := by
  apply le_antisymm
  · exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)
  · exact le_iInf (fun y => le_iInf (fun hy => hmin hy))

theorem localized_minimum (hX : IsClosed P.X) (hUb : Bornology.IsBounded U)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X)
    (hne : (P.MU U ν).Nonempty) : (P.SU U ν).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne
    (mu_compact hX hUb hls) ((hls 0).mono (fun _ h => h.1.1))
  exact ⟨x, hx, (vu_eq_of_min hx hmin).symm⟩

theorem base_localized_eq {μ : Measure ↥P.Ξ}
    (hne : (P.S μ).Nonempty) (hsub : P.S μ ⊆ U) :
    P.vU U μ = P.v μ ∧ P.SU U μ = P.S μ := by
  obtain ⟨x, hx⟩ := hne
  have hxU : x ∈ P.MU U μ := ⟨⟨hx.1.1, subset_closure (hsub hx)⟩, hx.1.2⟩
  have hv : P.vU U μ = P.v μ := by
    apply le_antisymm
    · exact (iInf_le_of_le x (iInf_le_of_le hxU le_rfl)).trans_eq hx.2
    · apply le_iInf
      intro y
      apply le_iInf
      intro hy
      exact iInf_le_of_le y (iInf_le_of_le (mu_subset_M hy) le_rfl)
  refine ⟨hv, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨mu_subset_M hy.1, hy.2.trans hv⟩
  · intro hy
    exact ⟨⟨⟨hy.1.1, subset_closure (hsub hy)⟩, hy.1.2⟩, hy.2.trans hv.symm⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ ν : Measure ↥P.Ξ}

theorem integral_abs_sub_le (j : Fin (d + 1)) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ P.X ∩ closure U) :
    EReal.abs (P.integral μ j x - P.integral ν j x) ≤ P.dFU U μ ν := by
  exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le j le_rfl))

theorem real_integral_discrepancy (j : Fin (d + 1)) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ P.X ∩ closure U)
    (hμ : P.integral μ j x ≠ ⊤ ∧ P.integral μ j x ≠ ⊥)
    (hν : P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥)
    {η : ℝ} (hη : 0 ≤ η) (hd : P.dFU U μ ν ≤ ENNReal.ofReal η) :
    |(P.integral μ j x).toReal - (P.integral ν j x).toReal| ≤ η := by
  have h := (integral_abs_sub_le (μ := μ) (ν := ν) j hx).trans hd
  rw [← EReal.coe_toReal hμ.1 hμ.2, ← EReal.coe_toReal hν.1 hν.2,
    ← EReal.coe_sub, EReal.abs_def] at h
  exact (ENNReal.ofReal_le_ofReal_iff hη).mp h

theorem discrepancy_constraint_transfer {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ P.X ∩ closure U)
    (hμ : ∀ j, P.integral μ j x ≠ ⊤ ∧ P.integral μ j x ≠ ⊥)
    (hν : ∀ j, P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥)
    {η : ℝ} (hη : 0 ≤ η) (hd : P.dFU U μ ν ≤ ENNReal.ofReal η)
    (hf : ∀ i : Fin d, P.integral μ i.succ x ≤ ((-η : ℝ) : EReal)) :
    x ∈ P.MU U ν := by
  refine ⟨hx, fun i => ?_⟩
  have hb := real_integral_discrepancy i.succ hx (hμ _) (hν _) hη hd
  have hh := hf i
  rw [← EReal.coe_toReal (hμ _).1 (hμ _).2, EReal.coe_le_coe_iff] at hh
  rw [← EReal.coe_toReal (hν _).1 (hν _).2, ← EReal.coe_zero, EReal.coe_le_coe_iff]
  linarith [(abs_sub_le_iff.mp hb).2]

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ ν : Measure ↥P.Ξ}

theorem metric_recovery (hX : IsClosed P.X)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X)
    {z x : EuclideanSpace ℝ (Fin m)} {a ε η : ℝ}
    (ha : 0 ≤ a) (hη : 0 ≤ η) (hreg : P.MetricRegularityEstimate μ z a ε)
    (hx : x ∈ P.X ∩ closedBall z ε) (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ ε)
    (hres : ∀ i, (P.integral μ i.succ x - (y i : EReal)).toENNReal ≤ ENNReal.ofReal η) :
    ∃ w ∈ P.My μ y, dist x w ≤ a * η := by
  have hb := hreg x hx y hy
  have hmax : (⨆ i : Fin d, (P.integral μ i.succ x - (y i : EReal)).toENNReal) ≤
      ENNReal.ofReal η := iSup_le hres
  have hbound : infEDist x (P.My μ y) ≤ ENNReal.ofReal (a * η) := by
    calc
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal η := hb.trans (by gcongr)
      _ = ENNReal.ofReal (a * η) := (ENNReal.ofReal_mul ha).symm
  exact exists_near_of_infEDist_le (my_closed hX hls y) x (mul_nonneg ha hη) hbound

theorem residual_of_real_bound {t c η : ℝ} (ht : t - c ≤ η) :
    ((t : EReal) - (c : EReal)).toENNReal ≤ ENNReal.ofReal η := by
  rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
  exact ENNReal.ofReal_le_ofReal ht

theorem strict_slack_recovery (hX : IsClosed P.X)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X)
    (hμ : ∀ j x, x ∈ P.X ∩ closure U → P.integral μ j x ≠ ⊤ ∧ P.integral μ j x ≠ ⊥)
    (hν : ∀ j x, x ∈ P.X ∩ closure U → P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ P.M μ) (hzU : z ∈ U)
    {a ε η : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hηε : η ≤ ε)
    (hreg : P.MetricRegularityEstimate μ z a ε)
    (hball : closedBall z (a * η) ⊆ U) (hd : P.dFU U μ ν ≤ ENNReal.ofReal η) :
    ∃ w ∈ P.MU U ν, dist z w ≤ a * η := by
  have hzK : z ∈ P.X ∩ closure U := ⟨hz.1, subset_closure hzU⟩
  have hres : ∀ i : Fin d,
      (P.integral μ i.succ z - ((-η : ℝ) : EReal)).toENNReal ≤ ENNReal.ofReal η := by
    intro i
    have hf := hμ i.succ z hzK
    have hh := hz.2 i
    rw [← EReal.coe_toReal hf.1 hf.2, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hh
    rw [← EReal.coe_toReal hf.1 hf.2]
    apply residual_of_real_bound
    linarith
  obtain ⟨w, hw, hdist⟩ := metric_recovery hX hls ha hη hreg
    ⟨hz.1, by simpa only [mem_closedBall, dist_self] using hε⟩
    (fun _ => -η) (fun _ => by simpa only [abs_neg, abs_of_nonneg hη] using hηε) hres
  have hwU : w ∈ U := hball (by simpa only [mem_closedBall, dist_comm] using hdist)
  have hwK : w ∈ P.X ∩ closure U := ⟨hw.1, subset_closure hwU⟩
  exact ⟨w, discrepancy_constraint_transfer hwK (fun j => hμ j w hwK)
    (fun j => hν j w hwK) hη hd hw.2, hdist⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology

namespace ProbMetricStab.General.PMSFresh

theorem exists_recovery_radius {E : Type*} [PseudoMetricSpace E] {U : Set E}
    (hU : IsOpen U) {z : E} (hz : z ∈ U) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ η : ℝ, 0 ≤ η → η < δ → closedBall z (a * η) ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let δ := min ε (r / (a + 1))
  have hδ : 0 < δ := lt_min hε (div_pos hr (by linarith))
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro η hη hηδ w hw
  apply hrU
  have hηr : η < r / (a + 1) := hηδ.trans_le (min_le_right _ _)
  have hp := (lt_div_iff₀ (show 0 < a + 1 by linarith)).mp hηr
  have hd : dist w z ≤ a * η := hw
  change dist w z < r
  nlinarith

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem upper_recovery (h : P.Thm22Assumptions U μ)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, ∀ η : ℝ,
      0 ≤ η → η < δ → P.dFU U μ ν ≤ ENNReal.ofReal η →
      ∃ w ∈ P.MU U ν, (P.integral ν 0 w).toReal ≤ (P.v μ).toReal + B * η := by
  obtain ⟨z, hz⟩ := h.S_nonempty
  have hzU := h.S_subset_U hz
  have hzK : z ∈ P.X ∩ closure U := ⟨hz.1.1, subset_closure hzU⟩
  by_cases hd : d = 0
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro ν hν η hη _ hdist
    have hzν : z ∈ P.MU U ν := by
      refine ⟨hzK, ?_⟩
      intro i
      exact Fin.elim0 (hd ▸ i)
    have hb := real_integral_discrepancy 0 hzK (hfin μ h.mem_PFU _ _ hzK)
      (hfin ν hν _ _ hzK) hη hdist
    refine ⟨z, hzν, ?_⟩
    rw [← hz.2]
    linarith [(abs_sub_le_iff.mp hb).2]
  · obtain ⟨K, hK⟩ := h.lipschitz (by omega)
    obtain ⟨a, ε, ha, hε, hreg⟩ := h.regular z hz
    obtain ⟨δ, hδ, hδε, hball⟩ := exists_recovery_radius h.U_open hzU ha hε
    refine ⟨(K : ℝ) * a + 1, δ, by positivity, hδ, ?_⟩
    intro ν hν η hη hηδ hdist
    obtain ⟨w, hw, hzw⟩ := strict_slack_recovery h.general.X_closed hls
      (hfin μ h.mem_PFU) (hfin ν hν) hz.1 hzU ha hε.le hη
      (hηδ.le.trans hδε) hreg (hball η hη hηδ) hdist
    have hwK := hw.1
    have hb := real_integral_discrepancy 0 hwK (hfin μ h.mem_PFU _ _ hwK)
      (hfin ν hν _ _ hwK) hη hdist
    have hlip := hK.dist_le_mul z hzK w hwK
    rw [Real.dist_eq] at hlip
    have hcost : (P.integral μ 0 w).toReal ≤ (P.integral μ 0 z).toReal + (K : ℝ) * (a * η) := by
      have hmul := mul_le_mul_of_nonneg_left hzw K.coe_nonneg
      linarith [(abs_sub_le_iff.mp hlip).2]
    refine ⟨w, hw, ?_⟩
    rw [← hz.2]
    nlinarith [(abs_sub_le_iff.mp hb).2]

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem localized_min_le {ν : Measure ↥P.Ξ} {x w : EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ P.SU U ν) (hw : w ∈ P.MU U ν)
    (hfx : P.integral ν 0 x ≠ ⊤ ∧ P.integral ν 0 x ≠ ⊥)
    (hfw : P.integral ν 0 w ≠ ⊤ ∧ P.integral ν 0 w ≠ ⊥) :
    (P.integral ν 0 x).toReal ≤ (P.integral ν 0 w).toReal := by
  have hh : P.integral ν 0 x ≤ P.integral ν 0 w :=
    hx.2.trans_le (iInf_le_of_le w (iInf_le_of_le hw le_rfl))
  exact EReal.toReal_le_toReal hh hfx.2 hfw.1

theorem perturbed_attainment (h : P.Thm22Assumptions U μ)
    (hls : ∀ ν ∈ P.PFU U, ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, ∀ η : ℝ,
      0 ≤ η → η < δ → P.dFU U μ ν ≤ ENNReal.ofReal η →
      (P.SU U ν).Nonempty ∧ ∀ x ∈ P.SU U ν,
        (P.integral ν 0 x).toReal ≤ (P.v μ).toReal + B * η := by
  obtain ⟨B, δ, hB, hδ, hr⟩ := upper_recovery h (hls μ h.mem_PFU) hfin
  refine ⟨B, δ, hB, hδ, ?_⟩
  intro ν hν η hη hηδ hd
  obtain ⟨w, hw, hcost⟩ := hr ν hν η hη hηδ hd
  refine ⟨localized_minimum h.general.X_closed h.U_bounded (hls ν hν) ⟨w, hw⟩, ?_⟩
  intro x hx
  exact (localized_min_le hx hw (hfin ν hν _ _ hx.1.1) (hfin ν hν _ _ hw.1)).trans hcost

end ProbMetricStab.General.PMSFresh


open Set Filter Topology

namespace ProbMetricStab.General.PMSFresh

theorem lsc_real_upper_limit {E : Type*} [TopologicalSpace E] {S : Set E}
    {f : E → EReal} (hS : IsClosed S) (hf : LowerSemicontinuousOn f S)
    {x : ℕ → E} {z : E} {b : ℕ → ℝ} {c : ℝ}
    (hx : Tendsto x atTop (𝓝 z)) (hb : Tendsto b atTop (𝓝 c))
    (hmem : ∀ n, x n ∈ S) (hle : ∀ n, f (x n) ≤ (b n : EReal)) :
    f z ≤ (c : EReal) := by
  have hc := (lowerSemicontinuousOn_iff_isClosed_epigraph hS).mp hf
  have ht : Tendsto (fun n => (x n, (b n : EReal))) atTop (𝓝 (z, (c : EReal))) :=
    hx.prodMk_nhds (continuous_coe_real_ereal.continuousAt.tendsto.comp hb)
  exact (hc.mem_of_tendsto ht (Eventually.of_forall (fun n => ⟨hmem n, hle n⟩))).2

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem base_value_finite (h : P.Thm22Assumptions U μ)
    (hfin : ∀ j x, x ∈ P.X ∩ closure U →
      P.integral μ j x ≠ ⊤ ∧ P.integral μ j x ≠ ⊥) :
    P.v μ ≠ ⊤ ∧ P.v μ ≠ ⊥ := by
  obtain ⟨z, hz⟩ := h.S_nonempty
  rw [← hz.2]
  exact hfin 0 z ⟨hz.1.1, subset_closure (h.S_subset_U hz)⟩

theorem minimizer_cluster (h : P.Thm22Assumptions U μ)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥)
    {ν : ℕ → Measure ↥P.Ξ} {η : ℕ → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin m)} {z : EuclideanSpace ℝ (Fin m)} {B : ℝ}
    (hν : ∀ n, ν n ∈ P.PFU U) (hη : ∀ n, 0 ≤ η n)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hd : ∀ n, P.dFU U μ (ν n) ≤ ENNReal.ofReal (η n))
    (hx : ∀ n, x n ∈ P.SU U (ν n)) (hxlim : Tendsto x atTop (𝓝 z))
    (hcost : ∀ n, (P.integral (ν n) 0 (x n)).toReal ≤ (P.v μ).toReal + B * η n) :
    z ∈ P.S μ := by
  have hxX : ∀ n, x n ∈ P.X := fun n => (hx n).1.1.1
  have hzX : z ∈ P.X := h.general.X_closed.mem_of_tendsto hxlim (Eventually.of_forall hxX)
  have hcon : ∀ i : Fin d, P.integral μ i.succ z ≤ 0 := by
    intro i
    have hh := lsc_real_upper_limit h.general.X_closed (hls i.succ) hxlim hηlim hxX
    apply le_trans (hh (fun n => ?_)) (by simp)
    have hfμ := hfin μ h.mem_PFU i.succ (x n) (hx n).1.1
    have hfν := hfin (ν n) (hν n) i.succ (x n) (hx n).1.1
    have he := real_integral_discrepancy i.succ (hx n).1.1 hfμ hfν (hη n) (hd n)
    have hzero : (P.integral (ν n) i.succ (x n)).toReal ≤ 0 := by
      simpa only [EReal.toReal_zero] using EReal.toReal_le_toReal ((hx n).1.2 i) hfν.2 (by simp)
    rw [← EReal.coe_toReal hfμ.1 hfμ.2]
    exact_mod_cast (show (P.integral μ i.succ (x n)).toReal ≤ η n by
      linarith [(abs_sub_le_iff.mp he).1])
  have hv := base_value_finite h (hfin μ h.mem_PFU)
  have hobj : P.integral μ 0 z ≤ P.v μ := by
    have ht : Tendsto (fun n => (P.v μ).toReal + (B + 1) * η n) atTop (𝓝 (P.v μ).toReal) := by
      simpa using tendsto_const_nhds.add (hηlim.const_mul (B + 1))
    have hh := lsc_real_upper_limit h.general.X_closed (hls 0) hxlim ht hxX
    rw [← EReal.coe_toReal hv.1 hv.2]
    apply hh
    intro n
    have hfμ := hfin μ h.mem_PFU 0 (x n) (hx n).1.1
    have hfν := hfin (ν n) (hν n) 0 (x n) (hx n).1.1
    have he := real_integral_discrepancy 0 (hx n).1.1 hfμ hfν (hη n) (hd n)
    rw [← EReal.coe_toReal hfμ.1 hfμ.2]
    exact_mod_cast (show (P.integral μ 0 (x n)).toReal ≤ (P.v μ).toReal + (B + 1) * η n by
      nlinarith [hcost n, (abs_sub_le_iff.mp he).1])
  have hzM : z ∈ P.M μ := ⟨hzX, hcon⟩
  exact ⟨hzM, le_antisymm hobj (iInf_le_of_le z (iInf_le_of_le hzM le_rfl))⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem eventual_repair (h : P.Thm22Assumptions U μ)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥)
    {ν : ℕ → Measure ↥P.Ξ} {η : ℕ → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin m)} {z : EuclideanSpace ℝ (Fin m)}
    (hν : ∀ n, ν n ∈ P.PFU U) (hη : ∀ n, 0 ≤ η n)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hd : ∀ n, P.dFU U μ (ν n) ≤ ENNReal.ofReal (η n))
    (hx : ∀ n, x n ∈ P.MU U (ν n)) (hxlim : Tendsto x atTop (𝓝 z))
    (hz : z ∈ P.S μ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ᶠ n in atTop, ∃ w ∈ P.MU U μ, dist (x n) w ≤ a * η n := by
  obtain ⟨a, ε, ha, hε, hreg⟩ := h.regular z hz
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (h.U_open.mem_nhds (h.S_subset_U hz))
  have hdist : Tendsto (fun n => dist (x n) z) atTop (𝓝 0) := by
    simpa using hxlim.dist (tendsto_const_nhds (x := z))
  have hsmall : ∀ᶠ n in atTop, dist (x n) z < ε ∧ dist (x n) z < r / 2 ∧ a * η n < r / 2 := by
    have haη : Tendsto (fun n => a * η n) atTop (𝓝 0) := by simpa using hηlim.const_mul a
    filter_upwards [hdist.eventually (gt_mem_nhds hε),
      hdist.eventually (gt_mem_nhds (half_pos hr)), haη.eventually (gt_mem_nhds (half_pos hr))]
      with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨a, ha, hsmall.mono ?_⟩
  intro n hn
  have hres : ∀ i : Fin d, (P.integral μ i.succ (x n) - ((0 : ℝ) : EReal)).toENNReal ≤
      ENNReal.ofReal (η n) := by
    intro i
    have hfμ := hfin μ h.mem_PFU i.succ (x n) (hx n).1
    have hfν := hfin (ν n) (hν n) i.succ (x n) (hx n).1
    have he := real_integral_discrepancy i.succ (hx n).1 hfμ hfν (hη n) (hd n)
    have hzero : (P.integral (ν n) i.succ (x n)).toReal ≤ 0 := by
      simpa only [EReal.toReal_zero] using EReal.toReal_le_toReal ((hx n).2 i) hfν.2 (by simp)
    rw [← EReal.coe_toReal hfμ.1 hfμ.2]
    apply residual_of_real_bound
    linarith [(abs_sub_le_iff.mp he).1]
  obtain ⟨w, hw, hwx⟩ := metric_recovery h.general.X_closed hls ha (hη n) hreg
    ⟨(hx n).1.1, hn.1.le⟩ (fun _ => 0) (fun _ => by simpa using hε.le) hres
  have hwU : w ∈ U := by
    apply hrU
    change dist w z < r
    have ht := dist_triangle w (x n) z
    rw [dist_comm w (x n)] at ht
    linarith [hn.2.1, hn.2.2]
  exact ⟨w, ⟨⟨hw.1, subset_closure hwU⟩, by simpa using hw.2⟩, hwx⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem uniform_repair (h : P.Thm22Assumptions U μ)
    (hls : ∀ ν ∈ P.PFU U, ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥) :
    ∃ a δ : ℝ, 0 ≤ a ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, ∀ η : ℝ,
      0 ≤ η → η < δ → P.dFU U μ ν ≤ ENNReal.ofReal η →
      ∀ x ∈ P.SU U ν, ∃ w ∈ P.MU U μ, dist x w ≤ a * η := by
  classical
  obtain ⟨B, δ₀, _hB, hδ₀, hatt⟩ := perturbed_attainment h hls hfin
  by_contra! hfail
  have hchoose : ∀ n : ℕ, ∃ ν ∈ P.PFU U, ∃ η : ℝ, 0 ≤ η ∧
      η < min δ₀ (1 / ((n : ℝ) + 1)) ∧ P.dFU U μ ν ≤ ENNReal.ofReal η ∧
      ∃ x ∈ P.SU U ν, ∀ w ∈ P.MU U μ, ((n : ℝ) + 1) * η < dist x w := by
    intro n
    exact hfail ((n : ℝ) + 1) (min δ₀ (1 / ((n : ℝ) + 1))) (by positivity)
      (lt_min hδ₀ (by positivity))
  choose ν hν η hη hsmall hd x hx hbad using hchoose
  have hηlim : Tendsto η atTop (𝓝 0) :=
    squeeze_zero hη (fun n => (hsmall n).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : IsCompact (P.X ∩ closure U) := h.U_bounded.isCompact_closure.inter_left h.general.X_closed
  obtain ⟨z, _, φ, hφ, hxlim⟩ := hK.tendsto_subseq (fun n => (hx n).1.1)
  have hcost : ∀ n, (P.integral (ν n) 0 (x n)).toReal ≤ (P.v μ).toReal + B * η n := by
    intro n
    exact (hatt (ν n) (hν n) (η n) (hη n) ((hsmall n).trans_le (min_le_left _ _)) (hd n)).2 _ (hx n)
  have hz : z ∈ P.S μ := minimizer_cluster h (hls μ h.mem_PFU) hfin
    (fun n => hν (φ n)) (fun n => hη (φ n)) (hηlim.comp hφ.tendsto_atTop)
    (fun n => hd (φ n)) (fun n => hx (φ n)) hxlim (fun n => hcost (φ n))
  obtain ⟨a, _ha, he⟩ := eventual_repair h (hls μ h.mem_PFU) hfin
    (fun n => hν (φ n)) (fun n => hη (φ n)) (hηlim.comp hφ.tendsto_atTop)
    (fun n => hd (φ n)) (fun n => (hx (φ n)).1) hxlim hz
  have hbig : ∀ᶠ n in atTop, a ≤ (φ n : ℝ) + 1 :=
    ((tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).eventually_ge_atTop a).mono (fun n hn => by
      change a ≤ (φ n : ℝ) at hn
      linarith)
  obtain ⟨n, hn, hn'⟩ := (he.and hbig).exists
  obtain ⟨w, hw, hdist⟩ := hn
  exact (hbad (φ n) w hw).not_ge (hdist.trans (mul_le_mul_of_nonneg_right hn' (hη (φ n))))

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem base_solution_compact (h : P.Thm22Assumptions U μ)
    (hls : ∀ j, LowerSemicontinuousOn (P.integral μ j) P.X) : IsCompact (P.S μ) := by
  have he : P.SU U μ = P.MU U μ ∩ {x | x ∈ P.X ∧ P.integral μ 0 x ≤ P.v μ} := by
    ext x
    have hv := (base_localized_eq h.S_nonempty h.S_subset_U).1
    constructor
    · intro hx
      exact ⟨hx.1, hx.1.1.1, (hx.2.trans hv).le⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      rw [hv]
      exact le_antisymm hx.2.2 (iInf_le_of_le x (iInf_le_of_le (mu_subset_M hx.1) le_rfl))
  rw [← (base_localized_eq h.S_nonempty h.S_subset_U).2, he]
  exact (mu_compact h.general.X_closed h.U_bounded hls).inter_right
    (closed_sublevel_on h.general.X_closed (hls 0) _)

theorem growth_enclosure (hS : IsCompact (P.S μ)) (hne : (P.S μ).Nonempty)
    {x y : EuclideanSpace ℝ (Fin m)} {η : ℝ≥0∞}
    (hy : y ∈ P.MU U μ) (hxy : edist x y ≤ η)
    (hgap : P.integral μ 0 y - P.v μ ≤ (η : EReal)) :
    x ∈ enlarge (P.S μ) (P.Ψ U μ η) := by
  obtain ⟨z, hz, he⟩ := hS.exists_infEDist_eq_edist hne y
  have hψ : P.ψ U μ (dist y z) ≤ (η : EReal) := by
    have hymem : y ∈ {w | w ∈ P.MU U μ ∧ ENNReal.ofReal (dist y z) ≤ infEDist w (P.S μ)} :=
      ⟨hy, by rw [he, edist_dist]⟩
    exact (iInf_le_of_le y (iInf_le_of_le hymem le_rfl)).trans hgap
  have hinv : edist y z ≤ P.ψinv U μ (η : EReal) := by
    rw [edist_dist]
    exact le_iSup_of_le (dist y z) (le_iSup_of_le ⟨dist_nonneg, hψ⟩ le_rfl)
  exact ⟨z, hz, (edist_triangle x y z).trans (add_le_add hxy hinv)⟩

end ProbMetricStab.General.PMSFresh


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem ereal_gap_of_real_bound {f v : EReal} {r : ℝ}
    (hf : f ≠ ⊤ ∧ f ≠ ⊥) (hv : v ≠ ⊤ ∧ v ≠ ⊥)
    (hr : 0 ≤ r) (hb : f.toReal - v.toReal ≤ r) :
    f - v ≤ (ENNReal.ofReal r : EReal) := by
  rw [← EReal.coe_toReal hf.1 hf.2, ← EReal.coe_toReal hv.1 hv.2,
    ← EReal.coe_sub, EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast hr),
    EReal.coe_le_coe_iff]
  exact hb

theorem deterministic_real_enclosure (h : P.Thm22Assumptions U μ)
    (hls : ∀ ν ∈ P.PFU U, ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥) :
    ∃ L δ : ℝ, 1 ≤ L ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, ∀ η : ℝ,
      0 ≤ η → η < δ → P.dFU U μ ν ≤ ENNReal.ofReal η →
      (P.SU U ν).Nonempty ∧ P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal (L * η))) := by
  obtain ⟨B, δ₀, hB, hδ₀, hatt⟩ := perturbed_attainment h hls hfin
  have hv := base_value_finite h (hfin μ h.mem_PFU)
  have hSc := base_solution_compact h (hls μ h.mem_PFU)
  by_cases hd : d = 0
  · refine ⟨B + 1, δ₀, by linarith, hδ₀, ?_⟩
    intro ν hν η hη hηδ he
    obtain ⟨hne, hcost⟩ := hatt ν hν η hη hηδ he
    refine ⟨hne, ?_⟩
    intro x hx
    have hxμ : x ∈ P.MU U μ := by
      refine ⟨hx.1.1, ?_⟩
      intro i
      exact Fin.elim0 (hd ▸ i)
    have hfμ := hfin μ h.mem_PFU 0 x hx.1.1
    have hfν := hfin ν hν 0 x hx.1.1
    have hdiff := real_integral_discrepancy 0 hx.1.1 hfμ hfν hη he
    apply growth_enclosure hSc h.S_nonempty hxμ (by simp)
    apply ereal_gap_of_real_bound hfμ hv (by positivity)
    nlinarith [hcost x hx, (abs_sub_le_iff.mp hdiff).1]
  · obtain ⟨K, hK⟩ := h.lipschitz (by omega)
    obtain ⟨a, δ₁, ha, hδ₁, hrepair⟩ := uniform_repair h hls hfin
    let L : ℝ := 1 + a + B + (K : ℝ) * a
    have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg ha]
    have haL : a ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg ha]
    refine ⟨L, min δ₀ δ₁, hL, lt_min hδ₀ hδ₁, ?_⟩
    intro ν hν η hη hηδ he
    obtain ⟨hne, hcost⟩ := hatt ν hν η hη (hηδ.trans_le (min_le_left _ _)) he
    refine ⟨hne, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hrepair ν hν η hη (hηδ.trans_le (min_le_right _ _)) he x hx
    have hfμx := hfin μ h.mem_PFU 0 x hx.1.1
    have hfνx := hfin ν hν 0 x hx.1.1
    have hfμy := hfin μ h.mem_PFU 0 y hy.1
    have hdiff := real_integral_discrepancy 0 hx.1.1 hfμx hfνx hη he
    have hlip := hK.dist_le_mul y hy.1 x hx.1.1
    rw [Real.dist_eq, dist_comm y x] at hlip
    apply growth_enclosure hSc h.S_nonempty hy
    · rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hxy.trans (mul_le_mul_of_nonneg_right haL hη))
    · apply ereal_gap_of_real_bound hfμy hv (mul_nonneg (by linarith) hη)
      have hmul := mul_le_mul_of_nonneg_left hxy K.coe_nonneg
      have hbudget : (B + 1 + (K : ℝ) * a) * η ≤ L * η := by
        apply mul_le_mul_of_nonneg_right _ hη
        dsimp [L]
        linarith
      nlinarith [hcost x hx, (abs_sub_le_iff.mp hdiff).1, (abs_sub_le_iff.mp hlip).1]

theorem deterministic_theorem_2_3 (h : P.Thm22Assumptions U μ)
    (hls : ∀ ν ∈ P.PFU U, ∀ j, LowerSemicontinuousOn (P.integral ν j) P.X)
    (hfin : ∀ ν ∈ P.PFU U, ∀ j x, x ∈ P.X ∩ closure U →
      P.integral ν j x ≠ ⊤ ∧ P.integral ν j x ≠ ⊥) :
    ∃ Lhat δ : ℝ, 1 ≤ Lhat ∧ 0 < δ ∧
      ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧ P.SU U ν ⊆ enlarge (P.S μ)
        (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by
  obtain ⟨L, δ, hL, hδ, hh⟩ := deterministic_real_enclosure h hls hfin
  refine ⟨L, δ, hL, hδ, ?_⟩
  intro ν hν hd
  have hdt : P.dFU U μ ν ≠ ⊤ := ne_top_of_lt hd
  have he : ENNReal.ofReal (P.dFU U μ ν).toReal = P.dFU U μ ν := ENNReal.ofReal_toReal hdt
  have hsmall : (P.dFU U μ ν).toReal < δ := by
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp (by simpa only [he] using hd)
  have hr := hh ν hν (P.dFU U μ ν).toReal ENNReal.toReal_nonneg hsmall (by rw [he])
  simpa only [ENNReal.ofReal_mul (show 0 ≤ L by linarith), he] using hr

end ProbMetricStab.General.PMSFresh

open MeasureTheory Set Metric
open scoped ENNReal

namespace ProbMetricStab.General.PMSFresh

theorem native_theorem_2_3 {m s d : ℕ} {P : Model m s d}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat δ : ℝ, 1 ≤ Lhat ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by
  have hKne : (P.X ∩ closure U).Nonempty := by
    obtain ⟨x, hx⟩ := h.S_nonempty
    exact ⟨x, hx.1.1, subset_closure (h.S_subset_U hx)⟩
  exact deterministic_theorem_2_3 h
    (fun ν hν j => integral_lsc h.general hν hKne j)
    (fun ν hν j x hx => integral_finite hν j hx)

end ProbMetricStab.General.PMSFresh

open MeasureTheory Set Metric
open scoped ENNReal

namespace ProbMetricStab.General

theorem theorem_2_3 {m s d : ℕ} {P : Model m s d}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat δ : ℝ, 1 ≤ Lhat ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by
  exact PMSFresh.native_theorem_2_3 h

end ProbMetricStab.General

open ProbMetricStab.General

theorem solution {m s d : ℕ} {P : Model m s d}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat δ : ℝ, 1 ≤ Lhat ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by
  exact ProbMetricStab.General.theorem_2_3 h
