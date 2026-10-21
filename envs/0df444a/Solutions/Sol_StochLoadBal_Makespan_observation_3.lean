-- Prove2me | solution 1 for StochLoadBal.Makespan.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T18:53:38.962911+00:00
-- url     : https://prove2.me/submissions/200aac6c-e2e5-47a5-aa6e-bc41fdecc244

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

namespace MachineClassResearch

variable {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
variable (P : Measure Ω) (X : Fin m → Fin n → Ω → ℝ) (b : ℝ)
variable (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)

include hy

lemma removable (L : Finset (Fin m)) (hL : L.Nonempty) :
    (L.filter (fun i => zLoad P X y i L.card ≤ b)).Nonempty := by
  classical
  by_contra h
  have hn : ∀ i ∈ L, b < zLoad P X y i L.card := by
    intro i hi
    by_contra hh
    exact h ⟨i, Finset.mem_filter.mpr ⟨hi, le_of_not_gt hh⟩⟩
  have hs := Finset.sum_lt_sum_of_nonempty hL hn
  have hu := hy.2.2.2.2 L hL
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith

lemma loop_invariant (fuel : ℕ) (L : Finset (Fin m)) (cls : Fin m → ℕ)
    (hsize : L.card ≤ fuel) :
    (∀ i ∉ L, classLoop P X b y fuel L cls i = cls i) ∧
    (∀ i ∈ L, 1 ≤ classLoop P X b y fuel L cls i ∧
      classLoop P X b y fuel L cls i ≤ L.card) ∧
    ∀ ℓ : ℕ, (L.filter (fun i => classLoop P X b y fuel L cls i ≤ ℓ)).card ≤ ℓ := by
  classical
  induction fuel generalizing L cls with
  | zero =>
    have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hL, classLoop]
  | succ fuel ih =>
    by_cases hL : L = ∅
    · simp [hL, classLoop]
    have hLpos : 0 < L.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hL)
    let F := L.filter (fun i => zLoad P X y i L.card ≤ b)
    have hF : F.Nonempty := removable P X b y hy L (Finset.nonempty_iff_ne_empty.mpr hL)
    have hFn : F ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hF
    have hFL : F ⊆ L := Finset.filter_subset _ _
    let S := L \ F
    have hSL : S ⊆ L := Finset.sdiff_subset
    have hScard : S.card ≤ fuel := by
      have heq := Finset.card_sdiff_add_card_eq_card hFL
      have hp := Finset.card_pos.mpr hF
      dsimp [S]
      omega
    let upd : Fin m → ℕ := fun i => if i ∈ F then L.card else cls i
    have hrec := ih S upd hScard
    have heq : classLoop P X b y (fuel+1) L cls =
        classLoop P X b y fuel S upd := by
      simp only [classLoop, if_neg hL]
      change (if F = ∅ then cls else classLoop P X b y fuel S upd) = _
      rw [if_neg hFn]
    rw [heq]
    have hfixed (i : Fin m) (hi : i ∈ F) :
        classLoop P X b y fuel S upd i = L.card := by
      have hn : i ∉ S := by simp [S, hi]
      simpa [upd, hi] using hrec.1 i hn
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hnS : i ∉ S := fun h => hi (hSL h)
      have hnF : i ∉ F := fun h => hi (hFL h)
      simpa [upd, hnF] using hrec.1 i hnS
    · intro i hi
      by_cases hiF : i ∈ F
      · rw [hfixed i hiF]
        exact ⟨hLpos, le_rfl⟩
      · have hiS : i ∈ S := Finset.mem_sdiff.mpr ⟨hi, hiF⟩
        exact ⟨(hrec.2.1 i hiS).1,
          (hrec.2.1 i hiS).2.trans (Finset.card_le_card hSL)⟩
    · intro ℓ
      by_cases hℓ : L.card ≤ ℓ
      · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hℓ
      · have hsub :
            L.filter (fun i => classLoop P X b y fuel S upd i ≤ ℓ) ⊆
            S.filter (fun i => classLoop P X b y fuel S upd i ≤ ℓ) := by
          intro i hi
          obtain ⟨hiL, hiℓ⟩ := Finset.mem_filter.mp hi
          have hiF : i ∉ F := by
            intro hiF
            rw [hfixed i hiF] at hiℓ
            exact hℓ hiℓ
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiL, hiF⟩, hiℓ⟩
        exact (Finset.card_le_card hsub).trans (hrec.2.2 ℓ)

end MachineClassResearch

theorem class_facts {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (b : ℝ) (y : Fin m → Fin n → ℝ)
    (hy : LPFeasible P X b y) :
    (∀ i, 1 ≤ machineClass P X b y i ∧ machineClass P X b y i ≤ m) ∧
    ∀ ℓ : ℕ, (Finset.univ.filter (fun i => machineClass P X b y i ≤ ℓ)).card ≤ ℓ := by
  have h := MachineClassResearch.loop_invariant P X b y hy m Finset.univ (fun _ => 0)
    (by simp)
  constructor
  · intro i
    simpa [machineClass] using h.2.1 i (Finset.mem_univ i)
  · exact h.2.2

#print axioms class_facts


-- Source mathematics: Anupam Gupta, Amit Kumar, Viswanath Nagarajan and Xiangkun Shen.
-- Formal model and integrability qualifications: mikedeng1; statement review: Shuze Chen.
-- Research directed by Alexander Richard Towell (queelius).
-- Formalization developed and checked with substantial OpenAI Codex assistance.
open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

namespace EffectiveSizeResearch
lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hm : Measurable Y)
    (hb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) : Integrable Y P := by
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg (hb ω).1] using (hb ω).2

lemma integral_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hm : Measurable Y)
    (hb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) :
    0 ≤ ∫ ω, Y ω ∂P ∧ ∫ ω, Y ω ∂P ≤ 1 := by
  refine ⟨integral_nonneg (fun ω => (hb ω).1), ?_⟩
  have hh := integral_mono (bounded_integrable P Y hm hb) (integrable_const (1 : ℝ))
    (fun ω => (hb ω).2)
  simpa using hh
end EffectiveSizeResearch

theorem effective_size_facts {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ Y : Ω → ℝ, Measurable Y → (∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) →
      0 ≤ effSize P k Y ∧ effSize P k Y ≤ 1) ∧
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
      Integrable (fun ω => Real.exp (Real.log k * Y ω)) P →
      ∫ ω, Y ω ∂P ≤ effSize P k Y) := by
  by_cases hk1 : k = 1
  · subst k
    simp only [effSize, ↓reduceIte]
    exact ⟨fun Y hm hb => EffectiveSizeResearch.integral_bounds P Y hm hb,
      fun _ _ _ _ => le_rfl⟩
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hl : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  constructor
  · intro Y hm hb
    have hlo (ω) : 1 ≤ Real.exp (Real.log k * Y ω) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hl.le (hb ω).1)
    have hup (ω) : Real.exp (Real.log k * Y ω) ≤ (k : ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (k : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_of_le_one_right hl.le (hb ω).2)
        _ = _ := Real.exp_log (zero_lt_one.trans hkR)
    have hint : Integrable (fun ω => Real.exp (Real.log k * Y ω)) P := by
      apply (integrable_const (k : ℝ)).mono'
        (Real.continuous_exp.measurable.comp (measurable_const.mul hm)).aestronglyMeasurable
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hup ω
    have hlow : 1 ≤ ∫ ω, Real.exp (Real.log k * Y ω) ∂P := by
      simpa using integral_mono (integrable_const (1 : ℝ)) hint hlo
    have hupper : (∫ ω, Real.exp (Real.log k * Y ω) ∂P) ≤ (k : ℝ) := by
      simpa using integral_mono hint (integrable_const (k : ℝ)) hup
    rw [effSize, if_neg hk1]
    refine ⟨div_nonneg (Real.log_nonneg hlow) hl.le, ?_⟩
    apply (div_le_one hl).mpr
    exact Real.log_le_log (zero_lt_one.trans_le hlow) hupper
  · intro Y _ hY hExp
    have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      (hY.const_mul (Real.log k)) hExp
    rw [integral_const_mul] at hj
    have hlog := Real.log_le_log (Real.exp_pos _) hj
    rw [Real.log_exp] at hlog
    rw [effSize, if_neg hk1]
    apply (le_div_iff₀ hl).mpr
    simpa [mul_comm] using hlog

#print axioms effective_size_facts

-- Lemma 2: the exact exponential-tail bound for independent job sizes.
theorem tail_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (k : ℕ) (hk : 2 ≤ k)
    (hint : ∀ i, Integrable (fun ω => Real.exp (Real.log k * Y i ω)) P)
    (b c : ℝ) (hb : ∑ i, effSize P k (Y i) ≤ b) :
    (P {ω | c ≤ ∑ i, Y i ω}).toReal ≤ (1 / (k : ℝ)) ^ (c - b) := by
  have hk1 : k ≠ 1 := by omega
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hl : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hs : Integrable (fun ω => Real.exp (Real.log k * (∑ i, Y i) ω)) P :=
    hind.integrable_exp_mul_sum hmeas (fun i _ => hint i)
  have ht := measure_ge_le_exp_cgf (μ := P) (X := ∑ i, Y i) c hl.le hs
  have he (i : Fin n) : cgf (Y i) P (Real.log k) = Real.log k * effSize P k (Y i) := by
    rw [effSize, if_neg hk1, cgf, mgf]
    field_simp
  have hc : cgf (∑ i, Y i) P (Real.log k) =
      Real.log k * ∑ i, effSize P k (Y i) := by
    rw [hind.cgf_sum hmeas (fun i _ => hint i)]
    simp_rw [he]
    rw [Finset.mul_sum]
  rw [hc] at ht
  have hr : (1 / (k : ℝ)) ^ (c - b) = Real.exp (-Real.log k * (c - b)) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    simp [Real.log_div]
  rw [hr]
  change P.real {ω | c ≤ ∑ i, Y i ω} ≤ _
  have htail : P.real {ω | c ≤ ∑ i, Y i ω} ≤
      Real.exp (-Real.log k * c + Real.log k * ∑ i, effSize P k (Y i)) := by
    simpa only [Finset.sum_apply] using ht
  exact htail.trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hb hl.le]))

#print axioms tail_bound

namespace TruncatedLoadResearch

lemma measurable_trunc : Measurable trunc := by
  exact measurable_id.ite (measurableSet_le measurable_id measurable_const) measurable_const

lemma trunc_bounds (x : ℝ) (hx : 0 ≤ x) : 0 ≤ trunc x ∧ trunc x ≤ 1 := by
  by_cases h : x ≤ 1 <;> simp [trunc, h, hx]

lemma exp_integrable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    Integrable (fun ω => Real.exp (Real.log k * Y ω)) P := by
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hl : 0 ≤ Real.log (k : ℝ) := (Real.log_pos hkR).le
  apply (integrable_const (k : ℝ)).mono'
    (Real.continuous_exp.measurable.comp (measurable_const.mul hY)).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖Real.exp (Real.log k * Y ω)‖ ≤ (k : ℝ)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (Real.log k) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right hl (hb ω).2)
    _ = _ := Real.exp_log (zero_lt_one.trans hkR)

end TruncatedLoadResearch

theorem solution {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) (i : Fin m) (α : ℝ) (hα : 0 ≤ α) :
    (P {ω | b + 1 + α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)}).toReal
      ≤ (machineClass P X b y i : ℝ) ^ (-α) := by
  classical
  let k := machineClass P X b y i
  have hk1 : 1 ≤ k := (class_facts hm P X b y hy).1 i |>.1
  by_cases hk : k = 1
  · change _ ≤ (k : ℝ) ^ (-α)
    rw [hk]
    simp only [Nat.cast_one, Real.one_rpow]
    exact measureReal_le_one
  have hk2 : 2 ≤ k := by omega
  let Y : Fin n → Ω → ℝ := fun j ω => if σ j = i then trunc (X i j ω) else 0
  have hY (j : Fin n) : Measurable (Y j) := by
    by_cases h : σ j = i
    · simpa [Y, h, Function.comp_def] using TruncatedLoadResearch.measurable_trunc.comp (hmeas i j)
    · simp only [Y, if_neg h]
      exact measurable_const
  have hYb (j : Fin n) (ω : Ω) : 0 ≤ Y j ω ∧ Y j ω ≤ 1 := by
    by_cases h : σ j = i
    · simpa [Y, h] using TruncatedLoadResearch.trunc_bounds (X i j ω) (hnn i j ω)
    · simp [Y, h]
  have hYi : iIndepFun Y P := by
    let g : Fin n → (Fin m → ℝ) → ℝ :=
      fun j z => if σ j = i then trunc (z i) else 0
    have hg (j : Fin n) : Measurable (g j) := by
      by_cases h : σ j = i
      · simpa [g, h, Function.comp_def] using
          TruncatedLoadResearch.measurable_trunc.comp (measurable_pi_apply i)
      · simp only [g, if_neg h]
        exact measurable_const
    simpa only [Function.comp_def, g, Y] using hind.comp g hg
  have heff (j : Fin n) : effSize P k (Y j) =
      if σ j = i then effSize P k (fun ω => trunc (X i j ω)) else 0 := by
    by_cases h : σ j = i <;> simp [Y, h, effSize]
  have hb : ∑ j, effSize P k (Y j) ≤ b+1 := by
    simp_rw [heff]
    simpa only [procTime, Finset.sum_filter] using hσ.2 i
  have htail := tail_bound P n Y hY hYi k hk2
    (fun j => TruncatedLoadResearch.exp_integrable P (Y j) (hY j) (hYb j) k hk2)
    (b+1) (b+1+α) hb
  have heq (ω : Ω) : (∑ j, Y j ω) =
      ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω) := by
    simp only [Y, Finset.sum_filter]
  have hsub : {ω | b+1+α < ∑ j, Y j ω} ⊆ {ω | b+1+α ≤ ∑ j, Y j ω} := by
    intro ω h
    change b+1+α < ∑ j, Y j ω at h
    change b+1+α ≤ ∑ j, Y j ω
    exact le_of_lt h
  have hbound := (measureReal_mono hsub).trans htail
  rw [show b+1+α-(b+1) = α by ring, one_div, ← Real.rpow_neg_eq_inv_rpow] at hbound
  simpa only [heq, k, Measure.real] using hbound

#print axioms solution
