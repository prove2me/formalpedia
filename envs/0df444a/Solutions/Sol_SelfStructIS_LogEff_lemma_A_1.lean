-- Prove2me | solution 1 for SelfStructIS.LogEff.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:28:06.048698+00:00
-- url     : https://prove2.me/submissions/741d5401-de4f-4a90-a12b-019d416cc69a

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SSISA1

open SelfStructIS.LogEff

set_option linter.unusedSectionVars false

variable {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d)

lemma meas_lt (s : ℝ) : MeasurableSet {y : Fin d → ℝ | s < y i} :=
  measurableSet_lt measurable_const (measurable_pi_apply i)

lemma surv_nonneg (s : ℝ) : 0 ≤ survival μ i s := ENNReal.toReal_nonneg

lemma surv_le_one (s : ℝ) : survival μ i s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma surv_anti {s s' : ℝ} (h : s ≤ s') : survival μ i s' ≤ survival μ i s :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun y (hy : s' < y i) => (lt_of_le_of_lt h hy : s < y i))

lemma hazard_nonneg (s : ℝ) : 0 ≤ hazard μ i s := by
  unfold hazard
  have := Real.log_nonpos (surv_nonneg μ i s) (surv_le_one μ i s)
  linarith

lemma surv_pos (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) (s : ℝ) : 0 < survival μ i s := by
  rcases (surv_nonneg μ i s).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    have h1 := hX (max X s) (le_max_left _ _)
    have h2 : survival μ i (max X s) = 0 :=
      le_antisymm (h ▸ surv_anti μ i (le_max_right X s)) (surv_nonneg μ i _)
    unfold hazard at h1
    rw [h2, Real.log_zero] at h1
    simp at h1

lemma hazard_mono (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) : Monotone (hazard μ i) := by
  intro s s' h
  unfold hazard
  have := Real.log_le_log (surv_pos μ i hev s') (surv_anti μ i h)
  linarith

lemma surv_eq_exp (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) (s : ℝ) :
    survival μ i s = Real.exp (-hazard μ i s) := by
  unfold hazard; rw [neg_neg, Real.exp_log (surv_pos μ i hev s)]

lemma hazard_tendsto {a : ℝ} (ha : 0 < a) (hrv : HeavyTailNV.Tail.IsRegularlyVarying (hazard μ i) a) :
    Tendsto (hazard μ i) atTop atTop := by
  have hmono := hazard_mono μ i hrv.1
  have h2 : (1 : ℝ) < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  set c : ℝ := (1 + (2 : ℝ) ^ a) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c < (2 : ℝ) ^ a := by rw [hc]; linarith
  have hev2 : ∀ᶠ x in atTop, c < hazard μ i (2 * x) / hazard μ i x :=
    (hrv.2 2 (by norm_num)).eventually (lt_mem_nhds hc2)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hev2.and (hrv.1.and (eventually_ge_atTop 1)))
  have hX1 : 1 ≤ X := (hX X le_rfl).2.2
  have hpow : ∀ n : ℕ, c ^ n * hazard μ i X ≤ hazard μ i (2 ^ n * X) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hge : X ≤ 2 ^ n * X := le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      obtain ⟨h1, h2', -⟩ := hX (2 ^ n * X) hge
      rw [lt_div_iff₀ h2'] at h1
      calc c ^ (n + 1) * hazard μ i X = c * (c ^ n * hazard μ i X) := by ring
        _ ≤ c * hazard μ i (2 ^ n * X) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ hazard μ i (2 * (2 ^ n * X)) := h1.le
        _ = hazard μ i (2 ^ (n + 1) * X) := by ring_nf
  have hHX : 0 < hazard μ i X := (hX X le_rfl).2.1
  rw [tendsto_atTop_atTop]
  intro b
  have htend : Tendsto (fun n : ℕ => c ^ n * hazard μ i X) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc1).atTop_mul_const hHX
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 htend b).exists
  exact ⟨2 ^ n * X, fun y hy => le_trans hn (le_trans (hpow n) (hmono hy))⟩


lemma qinv_self (hmono : Monotone (hazard μ i)) (x0 : ℝ)
    (hsm : StrictMonoOn (hazard μ i) (Set.Ioi x0)) (v : ℝ) (hv : x0 < v) :
    qinv μ i (hazard μ i v) = v := by
  unfold qinv
  apply IsLeast.csInf_eq
  refine ⟨show hazard μ i v ≤ hazard μ i v from le_refl _, fun x (hx : hazard μ i v ≤ hazard μ i x) => ?_⟩
  by_contra hlt
  push Not at hlt
  set x' := max x ((x0 + v) / 2)
  have hx'1 : x' ∈ Set.Ioi x0 := by
    show x0 < x'; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hx'2 : x' < v := max_lt hlt (by linarith)
  have := hsm hx'1 (show v ∈ Set.Ioi x0 from hv) hx'2
  have := hmono (le_max_left x ((x0 + v) / 2))
  linarith

lemma qinv_abs_le (hmono : Monotone (hazard μ i)) (t v : ℝ) (hv : 0 ≤ v)
    (h1 : t ≤ hazard μ i v) (h2 : hazard μ i 0 < t) : |qinv μ i t| ≤ v := by
  unfold qinv
  have hpos : ∀ x ∈ {x : ℝ | t ≤ hazard μ i x}, 0 ≤ x := by
    intro x hx
    by_contra h
    push Not at h
    have := hmono h.le
    have : t ≤ hazard μ i x := hx
    linarith
  have hne : ({x : ℝ | t ≤ hazard μ i x}).Nonempty := ⟨v, h1⟩
  have hb : BddBelow {x : ℝ | t ≤ hazard μ i x} := ⟨0, hpos⟩
  rw [abs_le]
  constructor
  · have := le_csInf hne hpos
    linarith
  · exact csInf_le hb h1

lemma nullZ (hcont : Continuous (hazard μ i)) (x0 : ℝ)
    (hsm : StrictMonoOn (hazard μ i) (Set.Ioi x0)) (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) :
    μ {x | hazard μ i (x i) ≤ 0} = 0 := by
  have hmono := hazard_mono μ i hev
  set Z := {s : ℝ | hazard μ i s ≤ 0} with hZ
  by_cases hne : Z.Nonempty
  · have hbdd : BddAbove Z := by
      refine ⟨x0 + 1, fun s (hs : hazard μ i s ≤ 0) => ?_⟩
      by_contra h
      push Not at h
      have := hsm (show x0 + 1 ∈ Set.Ioi x0 by simp) (show s ∈ Set.Ioi x0 by
        simp only [Set.mem_Ioi]; linarith) h
      have := hazard_nonneg μ i (x0 + 1)
      linarith
    have hclosed : IsClosed Z := isClosed_le hcont continuous_const
    have hb : sSup Z ∈ Z := hclosed.csSup_mem hne hbdd
    set b := sSup Z
    have hsub : {x : Fin d → ℝ | hazard μ i (x i) ≤ 0} ⊆ {y : Fin d → ℝ | b < y i}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      exact le_csSup hbdd hx
    refine measure_mono_null hsub ?_
    rw [prob_compl_eq_one_sub (meas_lt i b)]
    have hs1 : survival μ i b = 1 := by
      apply le_antisymm (surv_le_one μ i b)
      rw [surv_eq_exp μ i hev]
      have : hazard μ i b ≤ 0 := hb
      exact Real.one_le_exp (by linarith)
    have : μ {y : Fin d → ℝ | b < y i} = 1 := (ENNReal.toReal_eq_one_iff _).1 hs1
    rw [this]; simp
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have : {x : Fin d → ℝ | hazard μ i (x i) ≤ 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have : x i ∈ Z := h
      rw [hne] at this
      exact this
    rw [this, measure_empty]

lemma nullT (hcont : Continuous (hazard μ i)) (x0 : ℝ)
    (hsm : StrictMonoOn (hazard μ i) (Set.Ioi x0)) (hev : ∀ᶠ x in atTop, 0 < hazard μ i x)
    (r : ℝ) :
    μ {x | r < x i ∧ hazard μ i (x i) ≤ hazard μ i r} = 0 := by
  have hmono := hazard_mono μ i hev
  set T := {s : ℝ | r < s ∧ hazard μ i s ≤ hazard μ i r} with hT
  by_cases hne : T.Nonempty
  · have hbdd : BddAbove T := by
      refine ⟨max r x0 + 1, fun s hs => ?_⟩
      by_contra h
      push Not at h
      have h1 : max r x0 + 1 ∈ Set.Ioi x0 := by
        simp only [Set.mem_Ioi]; linarith [le_max_right r x0]
      have := hsm h1 (show s ∈ Set.Ioi x0 by
        simp only [Set.mem_Ioi]; linarith [le_max_right r x0]) h
      have := hmono (show r ≤ max r x0 + 1 by linarith [le_max_left r x0])
      have := hs.2
      linarith
    set b := sSup T
    have hclosed : IsClosed {s : ℝ | hazard μ i s ≤ hazard μ i r} :=
      isClosed_le hcont continuous_const
    have hbC : hazard μ i b ≤ hazard μ i r := by
      have := csSup_mem_closure hne hbdd
      have hsub : closure T ⊆ {s : ℝ | hazard μ i s ≤ hazard μ i r} :=
        hclosed.closure_subset_iff.2 (fun s hs => hs.2)
      exact hsub this
    obtain ⟨s0, hs0⟩ := hne
    have hrb : r < b := lt_of_lt_of_le hs0.1 (le_csSup hbdd hs0)
    have hsub : {x : Fin d → ℝ | r < x i ∧ hazard μ i (x i) ≤ hazard μ i r} ⊆
        {y : Fin d → ℝ | r < y i} \ {y : Fin d → ℝ | b < y i} := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      simp only [Set.mem_setOf_eq, not_lt]
      exact le_csSup hbdd hx
    refine measure_mono_null hsub ?_
    have hBA : {y : Fin d → ℝ | b < y i} ⊆ {y : Fin d → ℝ | r < y i} :=
      fun y (hy : b < y i) => (lt_trans hrb hy : r < y i)
    rw [measure_sdiff hBA (meas_lt i b).nullMeasurableSet (measure_ne_top _ _)]
    apply tsub_eq_zero_of_le
    have hsv : survival μ i r ≤ survival μ i b := by
      rw [surv_eq_exp μ i hev, surv_eq_exp μ i hev]
      exact Real.exp_le_exp.2 (by linarith)
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 hsv
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have : {x : Fin d → ℝ | r < x i ∧ hazard μ i (x i) ≤ hazard μ i r} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have : x i ∈ T := h
      rw [hne] at this
      exact this
    rw [this, measure_empty]

lemma ae_good (hcont : Continuous (hazard μ i)) (x0 : ℝ)
    (hsm : StrictMonoOn (hazard μ i) (Set.Ioi x0)) (hev : ∀ᶠ x in atTop, 0 < hazard μ i x) :
    ∀ᵐ x ∂μ, qinv μ i (hazard μ i (x i)) = x i ∧ 0 < hazard μ i (x i) := by
  have hmono := hazard_mono μ i hev
  rw [ae_iff]
  have cover : {x : Fin d → ℝ | ¬ (qinv μ i (hazard μ i (x i)) = x i ∧ 0 < hazard μ i (x i))} ⊆
      {x | hazard μ i (x i) ≤ 0} ∪
        ⋃ q : ℚ, {x | (q : ℝ) < x i ∧ hazard μ i (x i) ≤ hazard μ i (q : ℝ)} := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_and_or] at hx
    by_cases h0 : hazard μ i (x i) ≤ 0
    · exact Or.inl h0
    · right
      push Not at h0
      have hq : qinv μ i (hazard μ i (x i)) ≠ x i := by
        rcases hx with h | h
        · exact h
        · exact absurd h0 h
      set A := {y : ℝ | hazard μ i (x i) ≤ hazard μ i y} with hA
      have hxA : x i ∈ A := show hazard μ i (x i) ≤ hazard μ i (x i) from le_refl _
      have hy : ∃ y ∈ A, y < x i := by
        by_cases hb : BddBelow A
        · have hle : sInf A ≤ x i := csInf_le hb hxA
          have hlt : sInf A < x i := lt_of_le_of_ne hle hq
          exact exists_lt_of_csInf_lt ⟨x i, hxA⟩ hlt
        · rw [not_bddBelow_iff] at hb
          exact hb (x i)
      obtain ⟨y, hyA, hyx⟩ := hy
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hyx
      refine Set.mem_iUnion.2 ⟨q, hq2, ?_⟩
      exact le_trans hyA (hmono hq1.le)
  refine measure_mono_null cover (measure_union_null (nullZ μ i hcont x0 hsm hev) ?_)
  exact measure_iUnion_null fun q => nullT μ i hcont x0 hsm hev q

end SSISA1

open SelfStructIS.LogEff in
theorem solution (d : ℕ) (hd : 0 < d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ᶠ u in atTop, qinfty μ (tfun μ ρ u) = u ^ (1 / ρ)) ∧
      ∀ L Lstar : (Fin d → ℝ) → ℝ, Assumption21 μ L ρ Lstar →
        ∀ᶠ u in atTop, μ {x | u ≤ L x} =
          μ {x | (∀ i, 0 < ((tfun μ ρ u)⁻¹ • hazardVec μ x) i) ∧
            1 ≤ Lu μ L ρ u ((tfun μ ρ u)⁻¹ • hazardVec μ x)} := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  choose x0 hx0 using fun i => (h31 i).2.2.1
  have hev := fun i => (h31 i).2.2.2.1
  have hcont := fun i => (h31 i).2.1
  have hmono := fun i => SSISA1.hazard_mono μ i (hev i)
  have htend := fun i => SSISA1.hazard_tendsto μ i (h31 i).1 (h31 i).2.2.2
  have hv : Tendsto (fun u : ℝ => u ^ (1 / ρ)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have hP : ∀ᶠ u in atTop, 0 < u ∧ (∀ j, x0 j < u ^ (1 / ρ)) ∧
      ∀ i j, hazard μ i 0 < hazard μ j (u ^ (1 / ρ)) :=
    (eventually_gt_atTop 0).and
      ((eventually_all.2 fun j => hv.eventually (eventually_gt_atTop (x0 j))).and
        (eventually_all.2 fun i => eventually_all.2 fun j =>
          ((htend j).comp hv).eventually (eventually_gt_atTop _)))
  have key : ∀ u, (0 < u ∧ (∀ j, x0 j < u ^ (1 / ρ)) ∧
      ∀ i j, hazard μ i 0 < hazard μ j (u ^ (1 / ρ))) →
      0 < tfun μ ρ u ∧ qinfty μ (tfun μ ρ u) = u ^ (1 / ρ) := by
    rintro u ⟨hu, hx, hh⟩
    set v := u ^ (1 / ρ) with hvdef
    have hv0 : 0 ≤ v := Real.rpow_nonneg hu.le _
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun i => hazard μ i v)
    have ht : tfun μ ρ u = hazard μ j v := by rw [hj]; rfl
    have hle : ∀ i, tfun μ ρ u ≤ hazard μ i v := fun i => by
      show (⨅ k, hazard μ k v) ≤ _
      exact ciInf_le (Finite.bddBelow_range _) i
    refine ⟨by rw [ht]; linarith [hh j j, SSISA1.hazard_nonneg μ j 0], ?_⟩
    unfold qinfty qvec
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg hv0).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact SSISA1.qinv_abs_le μ i (hmono i) _ v hv0 (hle i) (by rw [ht]; exact hh i j)
    · rw [ht]
      have := norm_le_pi_norm (fun i => qinv μ i (hazard μ j v)) j
      rw [SSISA1.qinv_self μ j (hmono j) (x0 j) (hx0 j) v (hx j), Real.norm_of_nonneg hv0] at this
      exact this
  refine ⟨hP.mono fun u hu => (key u hu).2, fun L Lstar _ => ?_⟩
  have hgood : ∀ᵐ x ∂μ, ∀ i, qinv μ i (hazard μ i (x i)) = x i ∧ 0 < hazard μ i (x i) :=
    ae_all_iff.2 fun i => SSISA1.ae_good μ i (hcont i) (x0 i) (hx0 i) (hev i)
  refine hP.mono fun u hu => ?_
  have ht := (key u hu).1
  apply measure_congr
  refine Filter.eventuallyEq_set.2 (hgood.mono fun x hx => ?_)
  have hq : qvec μ (tfun μ ρ u • ((tfun μ ρ u)⁻¹ • hazardVec μ x)) = x := by
    rw [smul_inv_smul₀ ht.ne']
    funext i
    exact (hx i).1
  simp only [Set.mem_setOf_eq, Lu, hq]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hazardVec]
      exact mul_pos (inv_pos.2 ht) (hx i).2
    · rw [le_inv_mul_iff₀ hu.1]; simpa using h
  · rintro ⟨-, h⟩
    rw [le_inv_mul_iff₀ hu.1] at h
    simpa using h
