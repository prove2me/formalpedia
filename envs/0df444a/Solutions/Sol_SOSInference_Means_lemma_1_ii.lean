-- Prove2me | solution 1 for SOSInference.Means.lemma_1_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:43:10.36645+00:00
-- url     : https://prove2.me/submissions/d5b132a3-64db-4359-9e08-3a44ed73ba18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SOSInference_Means_Tarr
import Theorems.Thm_SOSInference_Means_lemma_1_i

open SOSInference.Means
open MeasureTheory

namespace SOSL1Aux

variable {l : ℕ} (M : Model l)

lemma tarr_le_iff (hl : 1 ≤ l) (n : ℕ) (i : Fin n) (lam : E l) (ω : M.Ω) {t : ℝ} (ht : 0 ≤ t) :
    Tarr M n i lam ω ≤ t ↔
      (∃ j, ‖Zfam M n ω j - (M.X i ω + (1 / 2 : ℝ) • lam)‖ ^ 2 ≤
          t ^ ((2 : ℝ) / l) / (n : ℝ) ^ ((2 : ℝ) / l) ∧ Zfam M n ω j ≠ M.X i ω) ∨
        (∀ j, Zfam M n ω j = M.X i ω) := by
  classical
  set D := Zfam M n ω
  set a := M.X i ω + (1 / 2 : ℝ) • lam
  set q : ℝ := (2 : ℝ) / l with hq
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hq0 : 0 < q := by rw [hq]; positivity
  set A := {s : ℝ | 0 ≤ s ∧ 1 ≤ Ncount M n i lam s ω} with hA
  have hAiff : ∀ s, s ∈ A ↔ 0 ≤ s ∧ ∃ j, ‖D j - a‖ ^ 2 ≤ s ^ q / (n : ℝ) ^ q ∧ D j ≠ M.X i ω := by
    intro s
    simp only [hA, Set.mem_setOf_eq, Ncount, Nat.one_le_iff_ne_zero, ne_eq,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, not_forall,
      not_not, exists_prop]
    rfl
  have hTarr : Tarr M n i lam ω = sInf A := rfl
  have hbdd : BddBelow A := ⟨0, fun s hs => hs.1⟩
  have hmono : ∀ s s', s ∈ A → s ≤ s' → s' ∈ A := by
    intro s s' hs hss'
    rw [hAiff] at hs ⊢
    obtain ⟨hs0, j, hj, hne⟩ := hs
    refine ⟨hs0.trans hss', j, le_trans hj ?_, hne⟩
    gcongr
  have hclosed : IsClosed A := by
    have : A = Set.Ici 0 ∩ ⋃ j ∈ (Finset.univ.filter fun j => D j ≠ M.X i ω),
        {s : ℝ | ‖D j - a‖ ^ 2 ≤ s ^ q / (n : ℝ) ^ q} := by
      ext s
      rw [hAiff]
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨h0, j, h1, h2⟩; exact ⟨h0, j, h2, h1⟩
      · rintro ⟨h0, j, h2, h1⟩; exact ⟨h0, j, h1, h2⟩
    rw [this]
    refine isClosed_Ici.inter (isClosed_biUnion_finset fun j _ => ?_)
    exact isClosed_le continuous_const ((Real.continuous_rpow_const hq0.le).div_const _)
  constructor
  · intro hT
    by_cases hAne : A.Nonempty
    · have hmem : sInf A ∈ A := hclosed.csInf_mem hAne hbdd
      have ht' := hmono _ t hmem (hTarr ▸ hT)
      rw [hAiff] at ht'
      exact Or.inl ht'.2
    · right
      intro j
      by_contra hne
      apply hAne
      have hev := ((tendsto_rpow_atTop hq0).eventually_ge_atTop
        (‖D j - a‖ ^ 2 * (n : ℝ) ^ q)).and (Filter.eventually_ge_atTop 0)
      obtain ⟨s, hs1, hs0⟩ := hev.exists
      have hnq : 0 < (n : ℝ) ^ q := by
        have : 0 < n := Fin.pos i
        exact Real.rpow_pos_of_pos (by exact_mod_cast this) q
      refine ⟨s, (hAiff s).mpr ⟨hs0, j, ?_, hne⟩⟩
      rw [le_div_iff₀ hnq]; exact hs1
  · rintro (⟨j, hj, hne⟩ | hall)
    · rw [hTarr]
      exact csInf_le hbdd ((hAiff t).mpr ⟨ht, j, hj, hne⟩)
    · have hAempty : A = ∅ := by
        ext s
        rw [hAiff]
        simp only [Set.mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ j _ hne
        exact hne (hall j)
      rw [hTarr, hAempty, Real.sInf_empty]
      exact ht


lemma tarr_nonneg (n : ℕ) (i : Fin n) (lam : E l) (ω : M.Ω) : 0 ≤ Tarr M n i lam ω :=
  Real.sInf_nonneg (fun _ hs => hs.1)

lemma tarr_meas (hl : 1 ≤ l) (hM : M.Standing) (n : ℕ) (i : Fin n) (lam : E l) :
    Measurable (Tarr M n i lam) := by
  classical
  apply measurable_of_Iic
  intro t
  by_cases ht : 0 ≤ t
  · have hset : Tarr M n i lam ⁻¹' Set.Iic t =
        (⋃ j, ({ω | ‖Zfam M n ω j - (M.X i ω + (1 / 2 : ℝ) • lam)‖ ^ 2 ≤
          t ^ ((2 : ℝ) / l) / (n : ℝ) ^ ((2 : ℝ) / l)} ∩ {ω | Zfam M n ω j ≠ M.X i ω})) ∪
        ⋂ j, {ω | Zfam M n ω j = M.X i ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_iInter]
      exact tarr_le_iff M hl n i lam ω ht
    rw [hset]
    have hZ : ∀ j, Measurable (fun ω => Zfam M n ω j) := by
      intro j
      rcases j with j | j
      · exact hM.measurable_X j
      · exact hM.measurable_Y j
    refine MeasurableSet.union (MeasurableSet.iUnion fun j => ?_) (MeasurableSet.iInter fun j => ?_)
    · refine MeasurableSet.inter ?_ ?_
      · exact measurableSet_le (((hZ j).sub ((hM.measurable_X i).add_const _)).norm.pow_const 2)
          measurable_const
      · exact (measurableSet_eq_fun (hZ j) (hM.measurable_X i)).compl
    · exact measurableSet_eq_fun (hZ j) (hM.measurable_X i)
  · have : Tarr M n i lam ⁻¹' Set.Iic t = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (lt_of_not_ge ht) (tarr_nonneg M n i lam ω)
    rw [this]; exact MeasurableSet.empty

end SOSL1Aux

namespace SOSL1Aux

/-- Layer-cake identity: `max(t² − x^α, 0) = ∫_0^t 2s·1[x ≤ s^{2/α}] ds`. -/
lemma layer {x t α : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hα : 0 < α) :
    max (t ^ 2 - x ^ α) 0 =
      ∫ s in Set.Ioc 0 t, 2 * s * (if x ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) := by
  set s0 := x ^ (α / 2) with hs0def
  have hs0 : 0 ≤ s0 := Real.rpow_nonneg hx _
  have hsq : s0 ^ 2 = x ^ α := by
    rw [hs0def, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have hiff : ∀ s : ℝ, 0 < s → (x ≤ s ^ ((2 : ℝ) / α) ↔ s0 ≤ s) := by
    intro s hs
    have hpos : 0 < α / 2 := by positivity
    rw [← Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hs.le _) hpos, ← Real.rpow_mul hs.le]
    rw [show (2 : ℝ) / α * (α / 2) = 1 by field_simp, Real.rpow_one]
  have hcongr : ∫ s in Set.Ioc 0 t, 2 * s * (if x ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) =
      ∫ s in Set.Ioc 0 t, (Set.Ici s0).indicator (fun s => 2 * s) s := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [Set.indicator, Set.mem_Ici]
    rw [if_congr (hiff s hs.1) rfl rfl]
    split_ifs <;> ring
  rw [hcongr, setIntegral_indicator measurableSet_Ici]
  rcases le_or_gt s0 t with hle | hlt
  · have hval : ∫ s in Set.Ioc 0 t ∩ Set.Ici s0, 2 * s = t ^ 2 - s0 ^ 2 := by
      have hI : ∫ s in Set.Ioc 0 t ∩ Set.Ici s0, 2 * s = ∫ s in Set.Ioc s0 t, 2 * s := by
        rcases hs0.eq_or_lt with h0 | h0
        · have : Set.Ioc 0 t ∩ Set.Ici s0 = Set.Ioc s0 t := by
            ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, ← h0]
            constructor
            · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.le⟩
          rw [this]
        · have : Set.Ioc 0 t ∩ Set.Ici s0 = Set.Icc s0 t := by
            ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
            constructor
            · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le h0 h1, h2⟩, h1⟩
          rw [this, integral_Icc_eq_integral_Ioc]
      rw [hI, ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
        integral_id]
      ring
    rw [hval, hsq]
    exact max_eq_left (by rw [← hsq]; nlinarith)
  · have : Set.Ioc 0 t ∩ Set.Ici s0 = ∅ := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨_, h2⟩, h3⟩; linarith
    rw [this, Measure.restrict_empty, integral_zero_measure]
    apply max_eq_right
    rw [← hsq]; nlinarith

end SOSL1Aux

namespace SOSL1Aux

lemma fubini_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → ℝ} (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω) {t α : ℝ} (ht : 0 ≤ t) (hα : 0 < α) :
    ∫ ω, max (t ^ 2 - T ω ^ α) 0 ∂P =
      ∫ s in Set.Ioc 0 t, 2 * s * (P {ω | T ω ≤ s ^ ((2 : ℝ) / α)}).toReal := by
  have hq : (0 : ℝ) ≤ 2 / α := by positivity
  have hrp : Measurable (fun s : ℝ => s ^ ((2 : ℝ) / α)) := (Real.continuous_rpow_const hq).measurable
  set ν := volume.restrict (Set.Ioc (0 : ℝ) t) with hν
  haveI : IsFiniteMeasure ν := ⟨by simp [hν, Real.volume_Ioc]⟩
  set f : Ω → ℝ → ℝ := fun ω s => 2 * s * (if T ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0)
    with hf
  have hfm : Measurable (Function.uncurry f) := by
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact Measurable.ite (measurableSet_le (hT.comp measurable_fst) (hrp.comp measurable_snd))
      measurable_const measurable_const
  have hμ : P.prod ν = (P.prod volume).restrict (Set.univ ×ˢ Set.Ioc 0 t) := by
    rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
  have hint : Integrable (Function.uncurry f) (P.prod ν) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (2 * t) ?_
    rw [hμ]
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ioc) ?_
    rintro ⟨ω, s⟩ ⟨-, hs⟩
    simp only [Function.uncurry_apply_pair, hf, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ 2 * s)]
    split_ifs
    · rw [abs_one, mul_one]; linarith [hs.2]
    · rw [abs_zero, mul_zero]; linarith
  have h1 : ∫ ω, max (t ^ 2 - T ω ^ α) 0 ∂P = ∫ ω, ∫ s, f ω s ∂ν ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => layer (hT0 ω) ht hα
  rw [h1, integral_integral_swap hint]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun s => ?_
  simp only [hf]
  rw [integral_const_mul]
  have : (fun ω => if T ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) =
      Set.indicator {ω | T ω ≤ s ^ ((2 : ℝ) / α)} 1 := by
    ext ω; simp [Set.indicator]
  rw [this, integral_indicator_one (measurableSet_le hT measurable_const), measureReal_def]

end SOSL1Aux

open SOSL1Aux in
theorem solution {l : ℕ} (hl : 1 ≤ l) (M : Model l) (hM : M.Standing) (lam : E l) (T : ℝ)
    (hT : 0 < T) (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2) :
    Filter.limsup (fun n : ℕ => ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          (max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
            ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P)| ∂M.P)
      Filter.atTop < ⊤ := by
  set T' : ℝ := T ^ ((2 : ℝ) / α) with hT'def
  have hT' : 0 < T' := Real.rpow_pos_of_pos hT _
  have h1 := lemma_1_i hl M hM lam T' hT'
  have hq : (0 : ℝ) ≤ 2 / α := by positivity
  have hrp : Measurable (fun s : ℝ => s ^ ((2 : ℝ) / α)) :=
    (Real.continuous_rpow_const hq).measurable
  have key : ∀ (n : ℕ) (ω : M.Ω), (⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          (max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
            ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P)|) ≤
      ENNReal.ofReal (T ^ 2) * ⨆ u ∈ Set.Icc (0 : ℝ) T',
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          ((if Tarr M n i lam ω ≤ u then (1 : ℝ) else 0) -
            (M.P {ω' | Tarr M n i lam ω' ≤ u}).toReal)| := by
    intro n ω
    set c : ℝ := ((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ with hc
    set Bf : ℝ → ℝ := fun u => c * ∑ i : Fin n,
          ((if Tarr M n i lam ω ≤ u then (1 : ℝ) else 0) -
            (M.P {ω' | Tarr M n i lam ω' ≤ u}).toReal) with hBf
    set Q := ⨆ u ∈ Set.Icc (0 : ℝ) T', ENNReal.ofReal |Bf u| with hQdef
    apply iSup₂_le
    intro t ht
    have hT2 : ENNReal.ofReal (T ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    by_cases hQ : Q = ⊤
    · rw [hQ, ENNReal.mul_top hT2]; exact le_top
    set q := Q.toReal with hqdef
    have hBq : ∀ u ∈ Set.Icc (0 : ℝ) T', |Bf u| ≤ q := by
      intro u hu
      exact (ENNReal.ofReal_le_iff_le_toReal hQ).mp
        (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T') => ENNReal.ofReal |Bf u|) u hu)
    have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
    -- the integral representation
    set ν := volume.restrict (Set.Ioc (0 : ℝ) t) with hν
    haveI : IsFiniteMeasure ν := ⟨by simp [hν, Real.volume_Ioc]⟩
    have hbdd : ∀ (g : ℝ → ℝ), Measurable g → (∀ s, |g s| ≤ 1) →
        Integrable (fun s => 2 * s * g s) ν := by
      intro g hg hg1
      refine Integrable.of_bound ((measurable_const.mul measurable_id).mul hg).aestronglyMeasurable
        (2 * t) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ 2 * s)]
      have := hg1 s
      have : 2 * s * |g s| ≤ 2 * s * 1 := by
        apply mul_le_mul_of_nonneg_left this; linarith [hs.1]
      linarith [hs.2]
    have hTm : ∀ i : Fin n, Measurable (Tarr M n i lam) := fun i => tarr_meas M hl hM n i lam
    have hPm : ∀ i : Fin n, Measurable (fun s : ℝ =>
        (M.P {ω' | Tarr M n i lam ω' ≤ s ^ ((2 : ℝ) / α)}).toReal) := by
      intro i
      have hmono : Monotone (fun u : ℝ => (M.P {ω' | Tarr M n i lam ω' ≤ u}).toReal) := by
        intro u u' huu'
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply measure_mono
        intro ω' hω'; exact le_trans hω' huu'
      exact hmono.measurable.comp hrp
    have hIm : ∀ i : Fin n, Measurable (fun s : ℝ =>
        if Tarr M n i lam ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) := by
      intro i
      exact Measurable.ite (measurableSet_le measurable_const hrp) measurable_const
        measurable_const
    have hint1 : ∀ i : Fin n, Integrable (fun s => 2 * s *
        (if Tarr M n i lam ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0)) ν := by
      intro i
      apply hbdd _ (hIm i)
      intro s; split_ifs <;> simp
    have hint2 : ∀ i : Fin n, Integrable (fun s => 2 * s *
        (M.P {ω' | Tarr M n i lam ω' ≤ s ^ ((2 : ℝ) / α)}).toReal) ν := by
      intro i
      apply hbdd _ (hPm i)
      intro s
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hrep : c * ∑ i : Fin n, (max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
          ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P) =
        ∫ s, 2 * s * Bf (s ^ ((2 : ℝ) / α)) ∂ν := by
      have hterm : ∀ i : Fin n, max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
          ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P =
          ∫ s, (2 * s * (if Tarr M n i lam ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) -
            2 * s * (M.P {ω' | Tarr M n i lam ω' ≤ s ^ ((2 : ℝ) / α)}).toReal) ∂ν := by
        intro i
        rw [integral_sub (hint1 i) (hint2 i), layer (tarr_nonneg M n i lam ω) ht.1 hα0,
          fubini_layer M.P (hTm i) (tarr_nonneg M n i lam) ht.1 hα0]
      have hint3 : ∀ i : Fin n, Integrable (fun s =>
          2 * s * (if Tarr M n i lam ω ≤ s ^ ((2 : ℝ) / α) then (1 : ℝ) else 0) -
            2 * s * (M.P {ω' | Tarr M n i lam ω' ≤ s ^ ((2 : ℝ) / α)}).toReal) ν :=
        fun i => (hint1 i).sub (hint2 i)
      simp only [hterm]
      rw [← integral_finset_sum _ (fun i _ => hint3 i), ← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun s => ?_
      simp only [hBf, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hrep]
    have hbound : |∫ s, 2 * s * Bf (s ^ ((2 : ℝ) / α)) ∂ν| ≤ ∫ s, 2 * s * q ∂ν := by
      rw [← Real.norm_eq_abs]
      have hiq : Integrable (fun s => 2 * s * q) ν := by
        have := (hbdd (fun _ => (1 : ℝ)) measurable_const (fun s => by simp)).mul_const q
        simpa using this
      apply norm_integral_le_of_norm_le hiq
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ 2 * s)]
      apply mul_le_mul_of_nonneg_left _ (by linarith [hs.1])
      apply hBq
      constructor
      · exact Real.rpow_nonneg hs.1.le _
      · rw [hT'def]
        exact Real.rpow_le_rpow hs.1.le (hs.2.trans ht.2) hq
    have hval : ∫ s, 2 * s * q ∂ν = t ^ 2 * q := by
      rw [integral_mul_const, hν, ← intervalIntegral.integral_of_le ht.1,
        intervalIntegral.integral_const_mul, integral_id]
      ring
    have htT : t ^ 2 * q ≤ T ^ 2 * q := by
      apply mul_le_mul_of_nonneg_right _ hq0
      exact pow_le_pow_left₀ ht.1 ht.2 2
    have hA : |∫ s, 2 * s * Bf (s ^ ((2 : ℝ) / α)) ∂ν| ≤ T ^ 2 * q := by
      linarith
    calc ENNReal.ofReal |∫ s, 2 * s * Bf (s ^ ((2 : ℝ) / α)) ∂ν| ≤ ENNReal.ofReal (T ^ 2 * q) :=
          ENNReal.ofReal_le_ofReal hA
      _ = ENNReal.ofReal (T ^ 2) * ENNReal.ofReal q := ENNReal.ofReal_mul (sq_nonneg _)
      _ = ENNReal.ofReal (T ^ 2) * Q := by rw [hqdef, ENNReal.ofReal_toReal hQ]
  calc Filter.limsup (fun n : ℕ => ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          (max (t ^ 2 - Tarr M n i lam ω ^ α) 0 -
            ∫ ω', max (t ^ 2 - Tarr M n i lam ω' ^ α) 0 ∂M.P)| ∂M.P) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ => ENNReal.ofReal (T ^ 2) * ∫⁻ ω, ⨆ u ∈ Set.Icc (0 : ℝ) T',
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          ((if Tarr M n i lam ω ≤ u then (1 : ℝ) else 0) -
            (M.P {ω' | Tarr M n i lam ω' ≤ u}).toReal)| ∂M.P) Filter.atTop := by
        apply Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n => ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono (key n)
    _ = ENNReal.ofReal (T ^ 2) * Filter.limsup (fun n : ℕ => ∫⁻ ω, ⨆ u ∈ Set.Icc (0 : ℝ) T',
        ENNReal.ofReal |((n : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ∑ i : Fin n,
          ((if Tarr M n i lam ω ≤ u then (1 : ℝ) else 0) -
            (M.P {ω' | Tarr M n i lam ω' ≤ u}).toReal)| ∂M.P) Filter.atTop :=
        ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1
