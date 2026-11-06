-- Prove2me | solution 2 for ProbMetricStab.MixedInt.theorem_2_2_d0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:01:56.415385+00:00
-- url     : https://prove2.me/submissions/23007990-c040-4331-83c4-ae72bc07a12b

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability
import Definitions.Def_ProbMetricStab_General_Setting
import Theorems.Thm_ProbMetricStab_General_theorem_2_2_d_zero



open MeasureTheory
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open MeasureTheory
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0

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
end ProbMetricStab.General.PMSd0

open MeasureTheory Filter
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0

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
end ProbMetricStab.General.PMSd0

open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open Set Metric MeasureTheory
namespace ProbMetricStab.General.PMSd0

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
end ProbMetricStab.General.PMSd0

open Set MeasureTheory
namespace ProbMetricStab.General.PMSd0

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
end ProbMetricStab.General.PMSd0

open Set Metric MeasureTheory
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open MeasureTheory Set
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
namespace ProbMetricStab.General.PMSd0
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
end ProbMetricStab.General.PMSd0


open Set Metric
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

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

end ProbMetricStab.General.PMSd0


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

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

end ProbMetricStab.General.PMSd0


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

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

end ProbMetricStab.General.PMSd0

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

variable {m s d : ℕ} {P : Model m s d}
  {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ}

theorem base_value_finite (h : P.Thm22Assumptions U μ)
    (hfin : ∀ j x, x ∈ P.X ∩ closure U →
      P.integral μ j x ≠ ⊤ ∧ P.integral μ j x ≠ ⊥) :
    P.v μ ≠ ⊤ ∧ P.v μ ≠ ⊥ := by
  obtain ⟨z, hz⟩ := h.S_nonempty
  rw [← hz.2]
  exact hfin 0 z ⟨hz.1.1, subset_closure (h.S_subset_U hz)⟩


end ProbMetricStab.General.PMSd0


open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

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

end ProbMetricStab.General.PMSd0

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

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

end ProbMetricStab.General.PMSd0


open MeasureTheory Set Metric
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

theorem thm23_d0 {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ ν ∈ P.PFU U,
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by
  obtain ⟨xbar, hxbar⟩ := h.S_nonempty
  have hxbarK : xbar ∈ P.X ∩ closure U := ⟨hxbar.1.1, subset_closure (h.S_subset_U hxbar)⟩
  have hKne : (P.X ∩ closure U).Nonempty := ⟨xbar, hxbarK⟩
  have hls := fun ν (hν : ν ∈ P.PFU U) j => integral_lsc h.general hν hKne j
  have hMU : ∀ ν : Measure ↥P.Ξ, P.MU U ν = P.X ∩ closure U := by
    intro ν
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => i.elim0⟩⟩
  have hv := base_value_finite h (fun j x hx => integral_finite h.mem_PFU j hx)
  have hSc := base_solution_compact h (hls μ h.mem_PFU)
  refine ⟨2, by norm_num, fun ν hν => ?_⟩
  have hne : (P.SU U ν).Nonempty :=
    localized_minimum h.general.X_closed h.U_bounded (hls ν hν) (by rw [hMU]; exact hKne)
  refine ⟨hne, fun x hx => ?_⟩
  have hxK : x ∈ P.X ∩ closure U := hx.1.1
  have hxμ : x ∈ P.MU U μ := by rw [hMU]; exact hxK
  by_cases hdt : P.dFU U μ ν = ⊤
  · refine ⟨xbar, hxbar, ?_⟩
    rw [hdt, ENNReal.mul_top (by norm_num)]
    simp [Model.Ψ]
  · set η := (P.dFU U μ ν).toReal with hηdef
    have hη : 0 ≤ η := ENNReal.toReal_nonneg
    have he : P.dFU U μ ν ≤ ENNReal.ofReal η := (ENNReal.ofReal_toReal hdt).ge
    have hfμx := integral_finite h.mem_PFU 0 hxK
    have hfνx := integral_finite hν 0 hxK
    have hfμb := integral_finite h.mem_PFU 0 hxbarK
    have hfνb := integral_finite hν 0 hxbarK
    have hd1 := real_integral_discrepancy 0 hxK hfμx hfνx hη he
    have hd2 := real_integral_discrepancy 0 hxbarK hfμb hfνb hη he
    have hmin : P.integral ν 0 x ≤ P.integral ν 0 xbar := by
      rw [hx.2]
      exact iInf_le_of_le xbar (iInf_le_of_le (by rw [hMU]; exact hxbarK) le_rfl)
    have hminR : (P.integral ν 0 x).toReal ≤ (P.integral ν 0 xbar).toReal :=
      EReal.toReal_le_toReal hmin hfνx.2 hfνb.1
    have hvR : (P.v μ).toReal = (P.integral μ 0 xbar).toReal := by rw [hxbar.2]
    have hrad : ENNReal.ofReal 2 * P.dFU U μ ν = ENNReal.ofReal (2 * η) := by
      rw [ENNReal.ofReal_mul (by norm_num), hηdef, ENNReal.ofReal_toReal hdt]
    rw [hrad]
    apply growth_enclosure hSc ⟨xbar, hxbar⟩ hxμ (by rw [edist_self]; exact zero_le')
    apply ereal_gap_of_real_bound hfμx hv (by positivity)
    rw [hvR]
    linarith [(abs_sub_le_iff.mp hd1).1, (abs_sub_le_iff.mp hd2).2]

end ProbMetricStab.General.PMSd0


open MeasureTheory Set Metric
open scoped ENNReal

namespace ProbMetricStab.General.PMSd0

/-- Berge upper semicontinuity of `S_𝒰` at `μ` for `d = 0`. -/
theorem berge_d0 {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    P.SUIsBergeUSCAt U μ := by
  obtain ⟨xbar, hxbar⟩ := h.S_nonempty
  have hxbarK : xbar ∈ P.X ∩ closure U := ⟨hxbar.1.1, subset_closure (h.S_subset_U hxbar)⟩
  have hKne : (P.X ∩ closure U).Nonempty := ⟨xbar, hxbarK⟩
  have hls := fun ν (hν : ν ∈ P.PFU U) j => integral_lsc h.general hν hKne j
  have hMU : ∀ ν : Measure ↥P.Ξ, P.MU U ν = P.X ∩ closure U := by
    intro ν
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => i.elim0⟩⟩
  have hv := base_value_finite h (fun j x hx => integral_finite h.mem_PFU j hx)
  have hbase := base_localized_eq h.S_nonempty h.S_subset_U
  have hcpt : IsCompact (P.X ∩ closure U) :=
    h.U_bounded.isCompact_closure.inter_left h.general.X_closed
  intro O hO hsub
  set K := (P.X ∩ closure U) \ O with hKdef
  have hKc : IsCompact K := hcpt.diff hO
  by_cases hKe : K.Nonempty
  · obtain ⟨x₀, hx₀K, hx₀min⟩ := LowerSemicontinuousOn.exists_isMinOn hKe hKc
      ((hls μ h.mem_PFU 0).mono (fun x hx => hx.1.1))
    have hf₀ := integral_finite h.mem_PFU 0 hx₀K.1
    -- the minimum on `K` exceeds `v(μ)`
    have hgt : (P.v μ).toReal < (P.integral μ 0 x₀).toReal := by
      have hle : P.v μ ≤ P.integral μ 0 x₀ := by
        rw [← hbase.1]
        exact iInf_le_of_le x₀ (iInf_le_of_le (by rw [hMU]; exact hx₀K.1) le_rfl)
      rcases (EReal.toReal_le_toReal hle hv.2 hf₀.1).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hEq : P.integral μ 0 x₀ = P.vU U μ := by
          rw [hbase.1]
          rw [← EReal.coe_toReal hf₀.1 hf₀.2, ← EReal.coe_toReal hv.1 hv.2, heq]
        exact hx₀K.2 (hsub ⟨by rw [hMU]; exact hx₀K.1, hEq⟩)
    set γ := (P.integral μ 0 x₀).toReal - (P.v μ).toReal with hγ
    have hγpos : 0 < γ := by rw [hγ]; linarith
    refine ⟨γ / 2, by positivity, fun ν hν hd => ?_⟩
    intro x hx
    by_contra hxO
    have hxK : x ∈ P.X ∩ closure U := hx.1.1
    have hdt : P.dFU U μ ν ≠ ⊤ := ne_top_of_lt hd
    set η := (P.dFU U μ ν).toReal with hηdef
    have hη : 0 ≤ η := ENNReal.toReal_nonneg
    have he : P.dFU U μ ν ≤ ENNReal.ofReal η := (ENNReal.ofReal_toReal hdt).ge
    have hηlt : η < γ / 2 := by
      have : ENNReal.ofReal η < ENNReal.ofReal (γ / 2) := by
        rw [hηdef, ENNReal.ofReal_toReal hdt]; exact hd
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 this
    have hfμx := integral_finite h.mem_PFU 0 hxK
    have hfνx := integral_finite hν 0 hxK
    have hfμb := integral_finite h.mem_PFU 0 hxbarK
    have hfνb := integral_finite hν 0 hxbarK
    have hd1 := real_integral_discrepancy 0 hxK hfμx hfνx hη he
    have hd2 := real_integral_discrepancy 0 hxbarK hfμb hfνb hη he
    have hmin : P.integral ν 0 x ≤ P.integral ν 0 xbar := by
      rw [hx.2]
      exact iInf_le_of_le xbar (iInf_le_of_le (by rw [hMU]; exact hxbarK) le_rfl)
    have hminR : (P.integral ν 0 x).toReal ≤ (P.integral ν 0 xbar).toReal :=
      EReal.toReal_le_toReal hmin hfνx.2 hfνb.1
    have hvR : (P.v μ).toReal = (P.integral μ 0 xbar).toReal := by rw [hxbar.2]
    have hK0 : P.integral μ 0 x₀ ≤ P.integral μ 0 x := hx₀min ⟨hxK, hxO⟩
    have hK0R : (P.integral μ 0 x₀).toReal ≤ (P.integral μ 0 x).toReal :=
      EReal.toReal_le_toReal hK0 hf₀.2 hfμx.1
    linarith [(abs_sub_le_iff.mp hd1).1, (abs_sub_le_iff.mp hd2).2]
  · refine ⟨1, one_pos, fun ν _ _ x hx => ?_⟩
    by_contra hxO
    exact hKe ⟨x, hx.1.1, hxO⟩

/-- For `d = 0`, `S_𝒰(ν)` is a CLM set w.r.t. `𝒰` for `ν` close to `μ`. -/
theorem clm_d0 {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧ P.SU U ν ⊆ U := by
  obtain ⟨xbar, hxbar⟩ := h.S_nonempty
  have hxbarK : xbar ∈ P.X ∩ closure U := ⟨hxbar.1.1, subset_closure (h.S_subset_U hxbar)⟩
  have hKne : (P.X ∩ closure U).Nonempty := ⟨xbar, hxbarK⟩
  have hMU : ∀ ν : Measure ↥P.Ξ, P.MU U ν = P.X ∩ closure U := by
    intro ν
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => i.elim0⟩⟩
  have hbase := base_localized_eq h.S_nonempty h.S_subset_U
  obtain ⟨δ, hδ, hB⟩ := berge_d0 h U h.U_open (by rw [hbase.2]; exact h.S_subset_U)
  refine ⟨δ, hδ, fun ν hν hd => ⟨?_, hB ν hν hd⟩⟩
  exact localized_minimum h.general.X_closed h.U_bounded
    (fun j => integral_lsc h.general hν hKne j) (by rw [hMU]; exact hKne)

end ProbMetricStab.General.PMSd0

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt.Bridge

open ProbMetricStab.MixedInt Set Metric

variable {m s : ℕ}

/-- The objective-only program `min ∫ f(ξ, x) ν(dξ)` as a `General.Model` with `d = 0`. -/
def model (Ξ : Set (EuclideanSpace ℝ (Fin s))) (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal) :
    ProbMetricStab.General.Model m s 0 :=
  ⟨X, Ξ, fun _ ξ x => f ξ.1 x⟩

/-- A measure on `ℝ^s` concentrated on `Ξ`, viewed as a measure on `Ξ`. -/
noncomputable def lift (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : Measure ↥Ξ :=
  ν.comap Subtype.val

section

variable {Ξ : Set (EuclideanSpace ℝ (Fin s))} {X : Set (EuclideanSpace ℝ (Fin m))}
  {f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal}

lemma lintegral_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (h : EuclideanSpace ℝ (Fin s) → ℝ≥0∞) :
    ∫⁻ ξ : ↥Ξ, h ξ ∂(lift Ξ ν) = ∫⁻ ξ, h ξ ∂ν := by
  rw [lift, lintegral_subtype_comap hΞ, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  exact hν

lemma expect_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (g : EuclideanSpace ℝ (Fin s) → EReal) :
    DupacovaWets.Consistency.expect (lift Ξ ν) (fun ξ => g ξ.1) =
      DupacovaWets.Consistency.expect ν g := by
  unfold DupacovaWets.Consistency.expect
  rw [lintegral_lift hΞ hν (fun ξ => (g ξ).toENNReal),
    lintegral_lift hΞ hν (fun ξ => (-g ξ).toENNReal)]

lemma integral_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (j : Fin 1) (x : EuclideanSpace ℝ (Fin m)) :
    (model Ξ X f).integral (lift Ξ ν) j x = intObj f ν x :=
  expect_lift hΞ hν (fun ξ => f ξ x)

lemma prob_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν ∈ ProbOn Ξ) : IsProbabilityMeasure (lift Ξ ν) := by
  have := hν.1
  refine isProbabilityMeasure_comap Subtype.val_injective ?_ (fun t ht => hΞ.subtype_image ht)
  rw [Subtype.range_coe, ae_iff]
  exact hν.2

lemma PFU_lift (hΞ : MeasurableSet Ξ) {U : Set (EuclideanSpace ℝ (Fin m))}
    {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν ∈ PFU Ξ f X U) :
    lift Ξ ν ∈ (model Ξ X f).PFU U := by
  obtain ⟨hP, h1, h2⟩ := hν
  refine ⟨prob_lift hΞ hP, fun j => ⟨fun r hr => ?_, ?_⟩⟩
  · have hset : {x : EuclideanSpace ℝ (Fin m) | x ∈ X ∧ ‖x‖ ≤ r} =
        X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r := by
      ext x; simp [mem_closedBall, dist_zero_right]
    have := h1 r hr
    change ⊥ < DupacovaWets.Consistency.expect (lift Ξ ν)
      (fun ξ => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) | x ∈ X ∧ ‖x‖ ≤ r}, f ξ.1 x)
    rw [hset, expect_lift hΞ hP.2 (fun ξ => ⨅ x ∈ X ∩ Metric.closedBall 0 r, f ξ x)]
    exact this
  · have heq : (⨆ x ∈ (model Ξ X f).X ∩ closure U, (model Ξ X f).integral (lift Ξ ν) j x) =
        ⨆ x ∈ X ∩ closure U, intObj f ν x :=
      iSup_congr fun x => iSup_congr fun _ => integral_lift hΞ hP.2 j x
    rw [heq]; exact h2

lemma normal_lift (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f) (j : Fin 1) :
    ProbMetricStab.General.IsNormalIntegrand ((model Ξ X f).f j) := by
  refine ⟨fun ω => hf.1 ω.1 ω.2, fun O hO => ?_⟩
  have h := (hf.2 O hO)
  convert measurable_subtype_coe h using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact ⟨fun h' => ⟨ω.2, h'⟩, fun h' => h'.2⟩

lemma M_model (ν : Measure ↥Ξ) : (model Ξ X f).M ν = X := by
  ext x; simp [ProbMetricStab.General.Model.M, model]

lemma MU_model (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥Ξ) :
    (model Ξ X f).MU U ν = X ∩ closure U := by
  ext x; simp [ProbMetricStab.General.Model.MU, model]

variable (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν Ξᶜ = 0)
include hΞ hν

lemma v_lift : (model Ξ X f).v (lift Ξ ν) = optVal f X ν := by
  unfold ProbMetricStab.General.Model.v optVal
  rw [M_model]
  exact iInf_congr fun x => iInf_congr fun _ => integral_lift hΞ hν 0 x

lemma S_lift : (model Ξ X f).S (lift Ξ ν) = solSet f X ν := by
  ext x
  simp only [ProbMetricStab.General.Model.S, solSet, M_model, Set.mem_ofPred_eq]
  rw [v_lift hΞ hν, integral_lift hΞ hν]

lemma vU_lift (U : Set (EuclideanSpace ℝ (Fin m))) :
    (model Ξ X f).vU U (lift Ξ ν) = locOptVal f X U ν := by
  unfold ProbMetricStab.General.Model.vU locOptVal
  rw [MU_model]
  exact iInf_congr fun x => iInf_congr fun _ => integral_lift hΞ hν 0 x

lemma SU_lift (U : Set (EuclideanSpace ℝ (Fin m))) :
    (model Ξ X f).SU U (lift Ξ ν) = locSolSet f X U ν := by
  ext x
  simp only [ProbMetricStab.General.Model.SU, locSolSet, MU_model, Set.mem_ofPred_eq]
  rw [vU_lift hΞ hν, integral_lift hΞ hν]

lemma dFU_lift (U : Set (EuclideanSpace ℝ (Fin m))) {μ : Measure (EuclideanSpace ℝ (Fin s))}
    (hμ : μ Ξᶜ = 0) :
    (model Ξ X f).dFU U (lift Ξ μ) (lift Ξ ν) = dFU f X U μ ν := by
  unfold ProbMetricStab.General.Model.dFU dFU
  refine iSup_congr fun x => iSup_congr fun _ => ?_
  simp only [integral_lift hΞ hμ, integral_lift hΞ hν, iSup_const]

lemma psiInv_lift (U : Set (EuclideanSpace ℝ (Fin m))) (t : ℝ≥0∞) :
    (model Ξ X f).ψinv U (lift Ξ ν) (t : EReal) = growthInv f X U ν t := by
  have hψ : ∀ τ : ℝ≥0, (model Ξ X f).ψ U (lift Ξ ν) (τ : ℝ) = growthFn f X U ν τ := by
    intro τ
    unfold ProbMetricStab.General.Model.ψ growthFn
    rw [MU_model, S_lift hΞ hν, v_lift hΞ hν, ENNReal.ofReal_coe_nnreal]
    exact iInf_congr fun x => iInf_congr fun _ => by rw [integral_lift hΞ hν]
  unfold ProbMetricStab.General.Model.ψinv growthInv
  apply le_antisymm
  · refine iSup₂_le fun τ hτ => ?_
    have h1 := hψ τ.toNNReal
    rw [Real.coe_toNNReal _ hτ.1] at h1
    have hτ2 : growthFn f X U ν τ.toNNReal ≤ (t : EReal) := by rw [← h1]; exact hτ.2
    refine le_iSup₂_of_le (f := fun (τ : ℝ≥0) (_ : growthFn f X U ν τ ≤ (t : EReal)) =>
      (τ : ℝ≥0∞)) τ.toNNReal hτ2 ?_
    rfl
  · refine iSup₂_le fun τ hτ => ?_
    refine le_iSup₂_of_le (f := fun (τ : ℝ) (_ : τ ∈ {τ : ℝ | 0 ≤ τ ∧
      (model Ξ X f).ψ U (lift Ξ ν) τ ≤ (t : EReal)}) => ENNReal.ofReal τ) (τ : ℝ)
      ⟨τ.2, by rw [hψ τ]; exact hτ⟩ ?_
    rw [ENNReal.ofReal_coe_nnreal]

lemma Psi_lift (U : Set (EuclideanSpace ℝ (Fin m))) (η : ℝ≥0∞) :
    (model Ξ X f).Ψ U (lift Ξ ν) η = PsiThm23 f X U ν η := by
  unfold ProbMetricStab.General.Model.Ψ PsiThm23
  rw [psiInv_lift hΞ hν]

end

/-- The assumptions of Theorem 2.2 transfer to the lifted model. -/
lemma thm22_lift {Ξ : Set (EuclideanSpace ℝ (Fin s))} (hΞ : IsClosed Ξ)
    {X : Set (EuclideanSpace ℝ (Fin m))} (hX : IsClosed X) (hXne : X.Nonempty)
    {f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal}
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    (model Ξ X f).Thm22Assumptions U (lift Ξ μ) := by
  have hΞm := hΞ.measurableSet
  have hμ0 : μ Ξᶜ = 0 := hμ.1.2
  refine ⟨⟨hXne, hX, hΞ, normal_lift hf⟩, PFU_lift hΞm hμ, ?_, hUo, hUb, ?_, ?_, ?_⟩
  · rw [S_lift hΞm hμ0]; exact hS
  · rw [S_lift hΞm hμ0]; exact hSU
  · intro h; omega
  · intro xbar _
    refine ⟨0, 1, le_rfl, one_pos, fun x hx y _ => ?_⟩
    have hxM : x ∈ (model Ξ X f).My (lift Ξ μ) y := ⟨hx.1, fun i => i.elim0⟩
    rw [infEDist_zero_of_mem hxM]
    exact bot_le

end ProbMetricStab.MixedInt.Bridge


open ProbMetricStab.MixedInt ProbMetricStab.MixedInt.Bridge in
theorem solution {m s : ℕ}
    (Ξ : Set (EuclideanSpace ℝ (Fin s))) (hΞ : IsClosed Ξ)
    (X : Set (EuclideanSpace ℝ (Fin m))) (hX : IsClosed X) (hXne : X.Nonempty)
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    (∀ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O → locSolSet f X U μ ⊆ O →
      ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal ε →
        locSolSet f X U ν ⊆ O) ∧
    (∀ ν ∈ PFU Ξ f X U,
      optVal f X μ ≠ ⊤ ∧ optVal f X μ ≠ ⊥ ∧ locOptVal f X U ν ≠ ⊤ ∧ locOptVal f X U ν ≠ ⊥ ∧
      ENNReal.ofReal |(optVal f X μ).toReal - (locOptVal f X U ν).toReal| ≤ dFU f X U μ ν) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal δ →
      IsCLMSet f X U ν) := by
  have hΞm := hΞ.measurableSet
  have hμ0 : μ Ξᶜ = 0 := hμ.1.2
  have hA := thm22_lift hΞ hX hXne hf hUo hUb hμ hS hSU
  have hBerge := ProbMetricStab.General.PMSd0.berge_d0 hA
  obtain ⟨δ, hδ, hmain⟩ := ProbMetricStab.General.PMSd0.clm_d0 hA
  have h0 := ProbMetricStab.General.theorem_2_2_d_zero hA
  refine ⟨fun O hO hsub => ?_, fun ν hν => ?_, ⟨δ, hδ, fun ν hν hd => ?_⟩⟩
  · rw [← SU_lift hΞm hμ0] at hsub
    obtain ⟨ε, hε, h⟩ := hBerge O hO hsub
    refine ⟨ε, hε, fun ν hν hd => ?_⟩
    have hν0 : ν Ξᶜ = 0 := hν.1.2
    rw [← dFU_lift hΞm hν0 U hμ0] at hd
    have := h (lift Ξ ν) (PFU_lift hΞm hν) hd
    rwa [SU_lift hΞm hν0] at this
  · have hν0 : ν Ξᶜ = 0 := hν.1.2
    obtain ⟨h1, h2, h3, h4, h5⟩ := h0 (lift Ξ ν) (PFU_lift hΞm hν)
    rw [v_lift hΞm hμ0] at h1 h2 h5
    rw [vU_lift hΞm hν0] at h3 h4 h5
    rw [dFU_lift hΞm hν0 U hμ0] at h5
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [← EReal.coe_toReal h1 h2, ← EReal.coe_toReal h3 h4, ← EReal.coe_sub,
      EReal.abs_def] at h5
    simpa only [EReal.toReal_coe] using h5
  · have hν0 : ν Ξᶜ = 0 := hν.1.2
    rw [← dFU_lift hΞm hν0 U hμ0] at hd
    obtain ⟨hne, hsub⟩ := hmain (lift Ξ ν) (PFU_lift hΞm hν) hd
    rw [SU_lift hΞm hν0] at hne hsub
    exact ⟨hUo, hne, hsub⟩
