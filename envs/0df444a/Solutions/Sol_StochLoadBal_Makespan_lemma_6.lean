-- Prove2me | solution 1 for StochLoadBal.Makespan.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T05:51:50.729362+00:00
-- url     : https://prove2.me/submissions/f4aaaad4-3ae2-4422-acfb-a7fbce6dff8e

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

theorem machine_tail {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
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

#print axioms machine_tail

namespace HighClassResearch

lemma class_power_sum (m : ℕ) (c : Fin m → ℕ)
    (hupper : ∀ i, c i ≤ m)
    (hcount : ∀ ℓ, (Finset.univ.filter (fun i => c i ≤ ℓ)).card ≤ ℓ)
    (α : ℝ) (hα : 2 < α) :
    (∑ i ∈ Finset.univ.filter (fun i => 3 ≤ c i), (c i : ℝ) ^ (-α)) ≤
      (2 : ℝ) ^ (2-α) / (α-2) := by
  classical
  let H := Finset.univ.filter (fun i => 3 ≤ c i)
  have hmem (i : Fin m) (hi : i ∈ H) : c i ∈ Finset.Icc 3 m :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hi).2, hupper i⟩
  have hgroup :
      (∑ i ∈ H, (c i : ℝ)^(-α)) =
        ∑ k ∈ Finset.Icc 3 m, ∑ i ∈ H, if c i = k then (k : ℝ)^(-α) else 0 := by
    calc
      _ = ∑ i ∈ H, ∑ k ∈ Finset.Icc 3 m,
          if c i = k then (k : ℝ)^(-α) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [hmem i hi]
      _ = _ := Finset.sum_comm
  have hfinite :
      (∑ i ∈ H, (c i : ℝ)^(-α)) ≤
        ∑ k ∈ Finset.Icc 3 m, (k : ℝ)^(1-α) := by
    rw [hgroup]
    apply Finset.sum_le_sum
    intro k hk
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega)
    have hs : H.filter (fun i => c i = k) ⊆ Finset.univ.filter (fun i => c i ≤ k) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.le⟩
    have hc : ((H.filter (fun i => c i = k)).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans (hcount k)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (k : ℝ) * (k : ℝ)^(-α) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hkpos.le _)
      _ = _ := by
        rw [show 1-α = 1+(-α) by ring, Real.rpow_add hkpos, Real.rpow_one]
  have hanti : AntitoneOn (fun x : ℝ => x^(1-α)) (Set.Icc (2 : ℝ) (m : ℝ)) := by
    intro x hx z hz hxz
    exact Real.rpow_le_rpow_of_nonpos (by have := hx.1; linarith) hxz (by linarith)
  have hint : IntegrableOn (fun x : ℝ => x^(1-α)) (Set.Ioi (2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hsum := hanti.sum_Ico_le_integral hint
    (fun t ht => Real.rpow_nonneg (by have := ht; change 2 < t at ht; linarith) _)
  have hsets : Finset.Ico (2+1) (m+1) = Finset.Icc 3 m := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hshift : (∑ k ∈ Finset.Ico 2 m, ((k+1 : ℕ) : ℝ)^(1-α)) =
      ∑ k ∈ Finset.Icc 3 m, (k : ℝ)^(1-α) := by
    simpa only [hsets] using
      Finset.sum_Ico_add' (fun k : ℕ => (k : ℝ)^(1-α)) 2 m 1
  rw [hshift] at hsum
  have heval : (∫ x : ℝ in Set.Ioi (2 : ℝ), x^(1-α)) =
      (2 : ℝ)^(2-α)/(α-2) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num),
      show 1-α+1 = 2-α by ring]
    have hn : α-2 ≠ 0 := by linarith
    have hn' : 2-α ≠ 0 := by linarith
    field_simp [hn, hn']
    <;> ring
  norm_num only [Nat.cast_ofNat] at hsum
  rw [heval] at hsum
  exact hfinite.trans hsum

end HighClassResearch

theorem high_class_tail {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) (α : ℝ) (hα : 2 < α) :
    (P {ω | ∃ i, 3 ≤ machineClass P X b y i ∧
        b + 1 + α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)}).toReal
      ≤ (2 : ℝ) ^ (2 - α) / (α - 2) := by
  classical
  let H := Finset.univ.filter (fun i => 3 ≤ machineClass P X b y i)
  let E : Fin m → Set Ω := fun i =>
    {ω | b+1+α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)}
  have heq : {ω | ∃ i, 3 ≤ machineClass P X b y i ∧
        b + 1 + α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)} =
      ⋃ i ∈ H, E i := by
    ext ω
    simp [H, E]
  change P.real _ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ i ∈ H, P.real (E i) := measureReal_biUnion_finset_le H E
    _ ≤ ∑ i ∈ H, (machineClass P X b y i : ℝ)^(-α) := by
      apply Finset.sum_le_sum
      intro i hi
      exact machine_tail hm P X hmeas hnn hint hind b y hy σ hσ i α (by linarith)
    _ ≤ _ := HighClassResearch.class_power_sum m (machineClass P X b y)
      (fun i => ((class_facts hm P X b y hy).1 i).2)
      (class_facts hm P X b y hy).2 α hα

#print axioms high_class_tail

namespace MakespanAssembly

lemma finite_layers (n : ℕ) (r t : ℝ) (ht : 0 ≤ t) (hr : r ≤ n) :
    r ≤ t + ∑ k ∈ Finset.range n, if t + (k : ℝ) < r then (1 : ℝ) else 0 := by
  classical
  let q := Nat.ceil (r - t)
  have hq : q ≤ n := Nat.ceil_le.mpr (by linarith)
  have hsum : (q : ℝ) = ∑ k ∈ Finset.range q, if t + (k : ℝ) < r then (1 : ℝ) else 0 := by
    have hh : ∀ k ∈ Finset.range q, t + (k : ℝ) < r := by
      intro k hk
      have := Nat.lt_ceil.mp (Finset.mem_range.mp hk)
      linarith
    calc
      (q : ℝ) = ∑ _k ∈ Finset.range q, (1 : ℝ) := by simp
      _ = _ := Finset.sum_congr rfl (fun k hk => by rw [if_pos (hh k hk)])
  have hs : (∑ k ∈ Finset.range q, if t + (k : ℝ) < r then (1 : ℝ) else 0) ≤
      ∑ k ∈ Finset.range n, if t + (k : ℝ) < r then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hq)
    intro k _ _
    split_ifs <;> norm_num
  have hceil : r-t ≤ (q : ℝ) := Nat.le_ceil _
  rw [← hsum] at hs
  linarith

lemma geometric_tail_bound (k : ℕ) :
    (2 : ℝ) ^ (2 - (3 + (k : ℝ))) / (3 + (k : ℝ) - 2) ≤
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hnum : 0 ≤ (2 : ℝ) ^ (2 - (3 + (k : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hden : (1 : ℝ) ≤ 3 + (k : ℝ) - 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hle := div_le_self hnum hden
  have heq : (2 : ℝ) ^ (2 - (3 + (k : ℝ))) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [show 2 - (3 + (k : ℝ)) = -((k+1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
    simp [pow_succ, one_div, mul_comm]
  exact hle.trans heq.le

lemma measurable_exc : Measurable exc := by
  exact measurable_id.ite (measurableSet_lt measurable_const measurable_id) measurable_const

lemma exc_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ exc x := by
  unfold exc
  split_ifs <;> linarith

lemma exc_le (x : ℝ) (hx : 0 ≤ x) : exc x ≤ x := by
  unfold exc
  split_ifs <;> linarith

lemma trunc_add_exc (x : ℝ) : trunc x + exc x = x := by
  by_cases h : x ≤ 1
  · simp [trunc, exc, h, not_lt.mpr h]
  · simp [trunc, exc, h, lt_of_not_ge h]

end MakespanAssembly

theorem solution {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (hb : 0 ≤ b) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) :
    expMakespan P X σ ≤ 4 * b + 10 := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let T : Fin m → Ω → ℝ := fun i ω => load (fun i j ω => trunc (X i j ω)) σ i ω
  let L := Finset.univ.filter (fun i => machineClass P X b y i ≤ 2)
  let F : Ω → ℝ := fun ω => ∑ i ∈ L, T i ω
  let E : ℕ → Set Ω := fun k => {ω | ∃ i, 3 ≤ machineClass P X b y i ∧ b+4+(k:ℝ) < T i ω}
  let J : ℕ → Ω → ℝ := fun k => (E k).indicator (fun _ => 1)
  let G : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, J k ω
  let W : Ω → ℝ := fun ω => ∑ j, exc (X (σ j) j ω)
  have hYmeas (i : Fin m) (j : Fin n) : Measurable (fun ω => trunc (X i j ω)) :=
    TruncatedLoadResearch.measurable_trunc.comp (hmeas i j)
  have hYbounds (i : Fin m) (j : Fin n) (ω : Ω) :
      0 ≤ trunc (X i j ω) ∧ trunc (X i j ω) ≤ 1 :=
    TruncatedLoadResearch.trunc_bounds _ (hnn i j ω)
  have hYint (i : Fin m) (j : Fin n) : Integrable (fun ω => trunc (X i j ω)) P :=
    EffectiveSizeResearch.bounded_integrable P _ (hYmeas i j) (hYbounds i j)
  have hTmeas (i : Fin m) : Measurable (T i) :=
    Finset.measurable_sum _ (fun j _ => hYmeas i j)
  have hTint (i : Fin m) : Integrable (T i) P := integrable_finsetSum _ (fun j _ => hYint i j)
  have hTnn (i : Fin m) (ω : Ω) : 0 ≤ T i ω :=
    Finset.sum_nonneg (fun j _ => (hYbounds i j ω).1)
  have hTbound (i : Fin m) (ω : Ω) : T i ω ≤ (n : ℝ) := by
    calc
      T i ω ≤ ∑ j ∈ Finset.univ.filter (fun j => σ j = i), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (hYbounds i j ω).2)
      _ ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; norm_num)
      _ = (n : ℝ) := by simp
  have hmean (i : Fin m) : (∫ ω, T i ω ∂P) ≤ b+1 := by
    have hclass := (class_facts hm P X b y hy).1 i |>.1
    have hj (j : Fin n) : (∫ ω, trunc (X i j ω) ∂P) ≤ procTime P X b y i j := by
      apply (effective_size_facts P (machineClass P X b y i) hclass).2 _ (hYmeas i j) (hYint i j)
      by_cases hk : machineClass P X b y i = 1
      · simp only [hk, Nat.cast_one, Real.log_one, zero_mul, Real.exp_zero]
        exact integrable_const 1
      · exact TruncatedLoadResearch.exp_integrable P _ (hYmeas i j) (hYbounds i j)
          _ (by omega)
    change (∫ ω, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω) ∂P) ≤ _
    rw [integral_finsetSum _ (fun j _ => hYint i j)]
    exact (Finset.sum_le_sum (fun j _ => hj j)).trans (hσ.2 i)
  have hFint : Integrable F P := integrable_finsetSum L (fun i _ => hTint i)
  have hFnn (ω : Ω) : 0 ≤ F ω := Finset.sum_nonneg (fun i _ => hTnn i ω)
  have hFmean : (∫ ω, F ω ∂P) ≤ 3*(b+1) := by
    have hcard : (L.card : ℝ) ≤ 3 := by
      have hc := (class_facts hm P X b y hy).2 2
      change L.card ≤ 2 at hc
      exact_mod_cast (show L.card ≤ 3 by omega)
    change (∫ ω, ∑ i ∈ L, T i ω ∂P) ≤ _
    rw [integral_finsetSum L (fun i _ => hTint i)]
    calc
      _ ≤ ∑ _i ∈ L, (b+1) := Finset.sum_le_sum (fun i _ => hmean i)
      _ = (L.card : ℝ)*(b+1) := by simp [nsmul_eq_mul]; ring
      _ ≤ 3*(b+1) := mul_le_mul_of_nonneg_right hcard (by linarith)
  have hEmeas (k : ℕ) : MeasurableSet (E k) := by
    simp only [E, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : 3 ≤ machineClass P X b y i
    · simpa only [hi, true_and] using measurableSet_lt measurable_const (hTmeas i)
    · simp only [hi, false_and, Set.setOf_false, MeasurableSet.empty]
  have hJint (k : ℕ) : Integrable (J k) P := (integrable_const (1:ℝ)).indicator (hEmeas k)
  have hJnn (k : ℕ) (ω : Ω) : 0 ≤ J k ω := by
    simp only [J, Set.indicator_apply]
    split_ifs <;> norm_num
  have hJmean (k : ℕ) : (∫ ω, J k ω ∂P) ≤ (1/2:ℝ)*(1/2:ℝ)^k := by
    have hi : (∫ ω, J k ω ∂P) = P.real (E k) := by
      simpa only [J, Pi.one_def] using (integral_indicator_one (μ := P) (hEmeas k))
    rw [hi]
    have htail := high_class_tail hm P X hmeas hnn hint hind b y hy σ hσ (3+(k:ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    rw [show b+1+(3+(k:ℝ)) = b+4+(k:ℝ) by ring] at htail
    exact htail.trans (MakespanAssembly.geometric_tail_bound k)
  have hGint : Integrable G P := integrable_finsetSum _ (fun k _ => hJint k)
  have hGnn (ω : Ω) : 0 ≤ G ω := Finset.sum_nonneg (fun k _ => hJnn k ω)
  have hGmean : (∫ ω, G ω ∂P) ≤ 1 := by
    change (∫ ω, ∑ k ∈ Finset.range n, J k ω ∂P) ≤ _
    rw [integral_finsetSum _ (fun k _ => hJint k)]
    have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => hJmean k)
    rw [← Finset.mul_sum] at hs
    have hgeo := sum_geometric_two_le n
    nlinarith
  have hhigh (i : Fin m) (hi : 3 ≤ machineClass P X b y i) (ω : Ω) :
      T i ω ≤ b+4+G ω := by
    have hl := MakespanAssembly.finite_layers n (T i ω) (b+4) (by linarith) (hTbound i ω)
    have hs : (∑ k ∈ Finset.range n, if b+4+(k:ℝ) < T i ω then (1:ℝ) else 0) ≤ G ω := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : b+4+(k:ℝ) < T i ω
      · have he : ω ∈ E k := ⟨i, hi, hk⟩
        simp [J, hk, Set.indicator_of_mem he]
      · simpa [hk] using hJnn k ω
    linarith
  have hExcInt (i : Fin m) (j : Fin n) : Integrable (fun ω => exc (X i j ω)) P := by
    apply (hint i j).mono' (MakespanAssembly.measurable_exc.comp (hmeas i j)).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖exc (X i j ω)‖ ≤ X i j ω
    rw [Real.norm_eq_abs, abs_of_nonneg (MakespanAssembly.exc_nonneg _ (hnn i j ω))]
    exact MakespanAssembly.exc_le _ (hnn i j ω)
  have hWint : Integrable W P := integrable_finsetSum _ (fun j _ => hExcInt (σ j) j)
  have hWmean : (∫ ω, W ω ∂P) ≤ 2 := by
    change (∫ ω, ∑ j, exc (X (σ j) j ω) ∂P) ≤ _
    rw [integral_finsetSum _ (fun j _ => hExcInt (σ j) j)]
    exact hσ.1
  have hpoint (ω : Ω) : makespan X σ ω ≤ F ω + (b+4) + G ω + W ω := by
    apply ciSup_le
    intro i
    have hexc : (∑ j ∈ Finset.univ.filter (fun j => σ j = i), exc (X i j ω)) ≤ W ω := by
      calc
        _ = ∑ j ∈ Finset.univ.filter (fun j => σ j = i), exc (X (σ j) j ω) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
        _ ≤ W ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => MakespanAssembly.exc_nonneg _ (hnn (σ j) j ω))
    have hsplit : load X σ i ω = T i ω +
        ∑ j ∈ Finset.univ.filter (fun j => σ j = i), exc (X i j ω) := by
      change (∑ j ∈ Finset.univ.filter (fun j => σ j = i), X i j ω) =
        (∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)) + _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => (MakespanAssembly.trunc_add_exc _).symm)
    by_cases hi : 3 ≤ machineClass P X b y i
    · have hh := hhigh i hi ω
      linarith [hFnn ω]
    · have hiL : i ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hlow : T i ω ≤ F ω := Finset.single_le_sum (fun j _ => hTnn j ω) hiL
      linarith [hGnn ω]
  have hloadmeas (i : Fin m) : Measurable (load X σ i) :=
    Finset.measurable_sum _ (fun j _ => hmeas i j)
  have hloadint (i : Fin m) : Integrable (load X σ i) P :=
    integrable_finsetSum _ (fun j _ => hint i j)
  have hloadnn (i : Fin m) (ω : Ω) : 0 ≤ load X σ i ω :=
    Finset.sum_nonneg (fun j _ => hnn i j ω)
  have hmsmeas : Measurable (makespan X σ) := Measurable.iSup hloadmeas
  have hmsint : Integrable (makespan X σ) P := by
    apply (integrable_finsetSum Finset.univ (fun i _ => hloadint i)).mono' hmsmeas.aestronglyMeasurable
    filter_upwards [] with ω
    let i0 : Fin m := ⟨0, by omega⟩
    have hmsnn : 0 ≤ makespan X σ ω := (hloadnn i0 ω).trans
      (le_ciSup (Set.finite_range (fun i => load X σ i ω)).bddAbove i0)
    rw [Real.norm_eq_abs, abs_of_nonneg hmsnn]
    apply ciSup_le
    intro i
    exact Finset.single_le_sum (fun j _ => hloadnn j ω) (Finset.mem_univ i)
  have hBint := ((hFint.add (integrable_const (b+4))).add hGint).add hWint
  have hbound := integral_mono hmsint hBint hpoint
  dsimp only [Pi.add_apply] at hbound
  rw [integral_add (f := fun ω => F ω + (b+4) + G ω) (g := W)
      ((hFint.add (integrable_const (b+4))).add hGint) hWint,
    integral_add (f := fun ω => F ω + (b+4)) (g := G)
      (hFint.add (integrable_const (b+4))) hGint,
    integral_add (f := F) (g := fun _ => b+4) hFint (integrable_const (b+4))] at hbound
  have hcint : (∫ _ω : Ω, b+4 ∂P) = b+4 := by simp
  rw [hcint] at hbound
  change (∫ ω, makespan X σ ω ∂P) ≤ _
  linarith

#print axioms solution
