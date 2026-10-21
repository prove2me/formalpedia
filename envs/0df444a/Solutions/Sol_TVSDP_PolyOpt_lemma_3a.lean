-- Prove2me | solution 1 for TVSDP.PolyOpt.lemma_3a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:20:30.865722+00:00
-- url     : https://prove2.me/submissions/353c4c11-8b5d-4758-b9eb-6e7e76cba5f7

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting
import Definitions.Def_TVSDP_PolyOpt_Mollifier

set_option autoImplicit false


namespace TVSDP.PolyOpt.Aux

open Matrix

def QF {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (β : ℝ) : Prop :=
  (∀ j k, M j k = M k j) ∧ ∀ w : Fin m → ℝ, β * ∑ j, w j ^ 2 ≤ ∑ j, ∑ k, w j * M j k * w k

lemma qf_iff {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (β : ℝ) :
    (M - β • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef ↔ QF M β := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hq : ∀ w : Fin m → ℝ, star w ⬝ᵥ ((M - β • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ w)
      = ∑ j, ∑ k, w j * M j k * w k - β * ∑ j, w j ^ 2 := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul]
    simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum, smul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · refine Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j k => ?_, fun w => ?_⟩
    · have := congrFun (congrFun h1 k) j
      simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply] at this
      by_cases hjk : j = k
      · subst hjk; rfl
      · simpa [hjk, Ne.symm hjk] using this
    · have := h2 w; rw [hq] at this; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun w => ?_⟩
    · ext j k
      simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, star_trivial]
      rw [h1 k j]
      by_cases hjk : j = k
      · subst hjk; simp
      · simp [hjk, Ne.symm hjk]
    · rw [hq]; linarith [h2 w]

lemma qf_perturb {m : ℕ} (M H : Matrix (Fin m) (Fin m) ℝ) (β θ : ℝ) (hM : QF M β)
    (hH : ∀ j k, H j k = H k j) (hθ : ∀ j k, |H j k - M j k| ≤ θ) (hθ0 : 0 ≤ θ)
    (hb : (m : ℝ) * θ ≤ β / 2) : QF H (β / 2) := by
  refine ⟨hH, fun w => ?_⟩
  have h1 := hM.2 w
  have key : ∑ j, ∑ k, w j * (H j k - M j k) * w k ≥ - (m * θ) * ∑ j, w j ^ 2 := by
    have : ∀ j k, w j * (H j k - M j k) * w k ≥ - (θ * ((w j ^ 2 + w k ^ 2) / 2)) := by
      intro j k
      have h := hθ j k
      have e1 : |w j * (H j k - M j k) * w k| ≤ θ * ((w j ^ 2 + w k ^ 2) / 2) := by
        rw [abs_mul, abs_mul]
        have : |w j| * |w k| ≤ (w j ^ 2 + w k ^ 2) / 2 := by
          nlinarith [sq_nonneg (|w j| - |w k|), sq_abs (w j), sq_abs (w k)]
        calc |w j| * |H j k - M j k| * |w k| = |H j k - M j k| * (|w j| * |w k|) := by ring
          _ ≤ θ * ((w j ^ 2 + w k ^ 2) / 2) := by
            apply mul_le_mul h this (by positivity) hθ0
      linarith [neg_abs_le (w j * (H j k - M j k) * w k)]
    calc ∑ j, ∑ k, w j * (H j k - M j k) * w k
        ≥ ∑ j : Fin m, ∑ k : Fin m, - (θ * ((w j ^ 2 + w k ^ 2) / 2)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => this j k
      _ = - (m * θ) * ∑ j, w j ^ 2 := by
          have e : ∑ j : Fin m, ∑ k : Fin m, (w j ^ 2 + w k ^ 2) / 2 = m * ∑ j, w j ^ 2 := by
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            rw [← Finset.mul_sum, ← Finset.sum_div]
            ring
          simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, e]
          ring
  have hs : ∑ j, ∑ k, w j * H j k * w k = ∑ j, ∑ k, w j * M j k * w k
      + ∑ j, ∑ k, w j * (H j k - M j k) * w k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hw : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [hs]
  nlinarith

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

lemma mol_J_eq (t : ℝ) : J t = cJ * expNegInvGlue (1 - t ^ 2) := by
  unfold J
  by_cases h : |t| < 1
  · rw [if_pos h]
    have hp : 0 < 1 - t ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one t |>.mpr h
      linarith
    unfold expNegInvGlue
    rw [if_neg (not_le.mpr hp)]
    congr 2
    rw [neg_div, one_div]
  · rw [if_neg h]
    have : 1 - t ^ 2 ≤ 0 := by
      have := one_le_sq_iff_one_le_abs t |>.mpr (not_lt.mp h)
      linarith
    rw [expNegInvGlue.zero_of_nonpos this, mul_zero]

lemma mol_cJ_nonneg : 0 ≤ cJ := by
  unfold cJ
  apply inv_nonneg.mpr
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact (Real.exp_pos _).le

lemma mol_glue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · exact zero_le_one
  · rw [Real.exp_le_one_iff]
    have : 0 < x := not_le.mp h
    have := inv_pos.mpr this
    linarith

lemma mol_J_nonneg (t : ℝ) : 0 ≤ J t := by
  rw [mol_J_eq]; exact mul_nonneg mol_cJ_nonneg (expNegInvGlue.nonneg _)

lemma mol_J_le (t : ℝ) : J t ≤ cJ := by
  rw [mol_J_eq]
  calc cJ * expNegInvGlue (1 - t ^ 2) ≤ cJ * 1 :=
        mul_le_mul_of_nonneg_left (mol_glue_le_one _) mol_cJ_nonneg
    _ = cJ := mul_one _

lemma mol_J_zero (t : ℝ) (h : 1 ≤ |t|) : J t = 0 := by
  unfold J; rw [if_neg (not_lt.mpr h)]

lemma mol_J_cont : Continuous J := by
  have : J = fun t => cJ * expNegInvGlue (1 - t ^ 2) := funext mol_J_eq
  rw [this]
  exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2))

lemma mol_intOn (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ s ∈ Icc (0:ℝ) 1, |g s| ≤ C) :
    IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply Measure.integrableOn_of_bounded (M := C) (by simp)
  · exact hg.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs]; exact hb s ⟨hs.1.le, hs.2⟩)

lemma mol_glue_cont : Continuous (fun t : ℝ => expNegInvGlue (1 - t ^ 2)) :=
  (expNegInvGlue.contDiff (n := 0)).continuous.comp (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2)

lemma mol_I_pos : 0 < ∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2)) := by
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-1 / (1 - t ^ 2))) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    have : IntegrableOn (fun t : ℝ => expNegInvGlue (1 - t ^ 2)) (Ioo (-1) 1) :=
      (mol_glue_cont.integrableOn_Icc (a := -1) (b := 1)).mono_set Ioo_subset_Icc_self
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have hp : 0 < 1 - t ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one t |>.mpr (abs_lt.mpr ht)
      linarith
    show expNegInvGlue (1 - t ^ 2) = _
    unfold expNegInvGlue
    rw [if_neg (not_le.mpr hp), neg_div, one_div]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => Real.exp_pos _) (by norm_num)

namespace TVSDP.PolyOpt.Aux

noncomputable def ρ (v : ℕ) (t : ℝ) : ℝ := Mv v (fun _ => 1) t

lemma cJ_pos : 0 < cJ := inv_pos.mpr mol_I_pos

lemma J_lower (u : ℝ) (hu : |u| ≤ 1/2) : cJ * Real.exp (-2) ≤ J u := by
  unfold J
  have h1 : |u| < 1 := by linarith
  rw [if_pos h1]
  apply mul_le_mul_of_nonneg_left _ cJ_pos.le
  apply Real.exp_le_exp.mpr
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hp : 0 < 1 - u ^ 2 := by linarith
  have : 1 / (1 - u ^ 2) ≤ 2 := by rw [div_le_iff₀ hp]; linarith
  rw [neg_div]; linarith

lemma K_cont (v : ℕ) (t : ℝ) : Continuous (fun s : ℝ => (v : ℝ) * J (v * (t - s))) :=
  continuous_const.mul (mol_J_cont.comp (by fun_prop))

lemma K_nonneg (v : ℕ) (t s : ℝ) : 0 ≤ (v : ℝ) * J (v * (t - s)) :=
  mul_nonneg (Nat.cast_nonneg _) (mol_J_nonneg _)

lemma K_zero (v : ℕ) (hv : 1 ≤ v) (t s : ℝ) (h : 1 / (v:ℝ) ≤ |t - s|) :
    (v : ℝ) * J (v * (t - s)) = 0 := by
  have hvpos : (0:ℝ) < v := by exact_mod_cast hv
  rw [mol_J_zero, mul_zero]
  rw [abs_mul, abs_of_pos hvpos]
  rw [div_le_iff₀ hvpos] at h; linarith

lemma Kint (v : ℕ) (t : ℝ) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (fun s => (v : ℝ) * J (v * (t - s)) * f s) volume 0 1 :=
  hf.continuousOn_mul (K_cont v t).continuousOn

lemma sub_interval (v : ℕ) (hv : 1 ≤ v) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b - a = 1 / (2 * v) ∧
      ∀ s ∈ Icc a b, |(v:ℝ) * (t - s)| ≤ 1 / 2 := by
  have hvpos : (0:ℝ) < v := by exact_mod_cast hv
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hh : 1 / (2 * (v:ℝ)) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hh0 : 0 < 1 / (2 * (v:ℝ)) := by positivity
  have key : ∀ s, |t - s| ≤ 1 / (2 * v) → |(v:ℝ) * (t - s)| ≤ 1 / 2 := by
    intro s hs
    rw [abs_mul, abs_of_pos hvpos]
    calc (v:ℝ) * |t - s| ≤ v * (1 / (2 * v)) := mul_le_mul_of_nonneg_left hs hvpos.le
      _ = 1 / 2 := by field_simp
  by_cases h : t ≤ 1 / 2
  · refine ⟨t, t + 1 / (2 * v), ht.1, by linarith, by linarith, by ring, fun s hs => key s ?_⟩
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  · refine ⟨t - 1 / (2 * v), t, by linarith, by linarith, ht.2, by ring, fun s hs => key s ?_⟩
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

lemma ρ_lower (v : ℕ) (hv : 1 ≤ v) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    cJ * Real.exp (-2) / 2 ≤ ρ v t := by
  obtain ⟨a, b, ha, hab, hb, hlen, hs⟩ := sub_interval v hv t ht
  have hvpos : (0:ℝ) < v := by exact_mod_cast hv
  unfold ρ Mv
  simp only [mul_one]
  have hint : IntervalIntegrable (fun s : ℝ => (v : ℝ) * J (v * (t - s))) volume 0 1 :=
    (K_cont v t).intervalIntegrable _ _
  have h1 : ∫ s in a..b, (v : ℝ) * J (v * (t - s)) ≤ ∫ s in (0:ℝ)..1, (v : ℝ) * J (v * (t - s)) :=
    intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall fun s => K_nonneg v t s) hint
  have h2 : ∫ s in a..b, ((v : ℝ) * (cJ * Real.exp (-2))) ≤ ∫ s in a..b, (v : ℝ) * J (v * (t - s)) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const
      ((K_cont v t).intervalIntegrable _ _)
      (fun s hs' => mul_le_mul_of_nonneg_left (J_lower _ (hs s hs')) hvpos.le)
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h2
  have : 1 / (2 * (v:ℝ)) * ((v:ℝ) * (cJ * Real.exp (-2))) = cJ * Real.exp (-2) / 2 := by
    field_simp
  linarith

lemma ρ_pos (v : ℕ) (hv : 1 ≤ v) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < ρ v t :=
  lt_of_lt_of_le (by have := cJ_pos; positivity) (ρ_lower v hv t ht)

lemma ρ_eq (v : ℕ) (t : ℝ) : ρ v t = ∫ s in (0:ℝ)..1, (v : ℝ) * J (v * (t - s)) := by
  unfold ρ Mv; simp only [mul_one]

lemma kbound (v : ℕ) (hv : 1 ≤ v) (t : ℝ) (h : ℝ → ℝ)
    (hh : IntervalIntegrable h volume 0 1) (ω : ℝ)
    (hω : ∀ s ∈ Icc (0:ℝ) 1, |t - s| < 1 / (v:ℝ) → |h s| ≤ ω) :
    |∫ s in (0:ℝ)..1, (v : ℝ) * J (v * (t - s)) * h s| ≤ ω * ρ v t := by
  rw [ρ_eq, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  apply intervalIntegral.integral_mono_on zero_le_one (Kint v t h hh).abs
    ((K_cont v t).intervalIntegrable _ _ |>.const_mul ω)
  intro s hs
  rw [abs_mul, abs_of_nonneg (K_nonneg v t s)]
  by_cases hts : |t - s| < 1 / (v:ℝ)
  · rw [mul_comm ω]
    exact mul_le_mul_of_nonneg_left (hω s hs hts) (K_nonneg v t s)
  · rw [K_zero v hv t s (not_lt.mp hts)]; simp

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

lemma iisum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ S, f i x) volume a b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma qf_avg {m : ℕ} (v : ℕ) (hv : 1 ≤ v) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (M : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hint : ∀ j k, IntervalIntegrable (fun s => M s j k) volume 0 1) (β : ℝ)
    (hM : ∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) 1)), QF (M s) β) :
    QF (Matrix.of fun j k => (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * M s j k) / ρ v t) β := by
  have hρ := ρ_pos v hv t ht
  have hM' : ∀ᵐ s ∂volume, s ∈ Icc (0:ℝ) 1 → QF (M s) β := (ae_restrict_iff' measurableSet_Icc).mp hM
  refine ⟨fun j k => ?_, fun w => ?_⟩
  · simp only [Matrix.of_apply]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hM'] with s hs hs'
    rw [uIoc_of_le zero_le_one] at hs'
    rw [(hs ⟨hs'.1.le, hs'.2⟩).1 j k]
  · simp only [Matrix.of_apply]
    have e : ∑ j, ∑ k, w j * ((∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * M s j k) / ρ v t) * w k
        = (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (∑ j, ∑ k, w j * M s j k * w k)) / ρ v t := by
      have hI : ∀ j k, IntervalIntegrable
          (fun s => (v:ℝ) * J (v * (t - s)) * (w j * M s j k * w k)) volume 0 1 := by
        intro j k
        exact Kint v t _ (((hint j k).const_mul (w j)).mul_const (w k))
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum (fun j _ => ?_)]
      · rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum (fun k _ => hI j k), Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : ∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (w j * M s j k * w k)
            = (w j * w k) * ∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * M s j k := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1; ext s; ring
        rw [this]; field_simp
      · exact iisum _ _ _ _ fun k _ => hI j k
    rw [e, le_div_iff₀ hρ, ρ_eq, ← intervalIntegral.integral_const_mul]
    have hQ : IntervalIntegrable (fun s => ∑ j, ∑ k, w j * M s j k * w k) volume 0 1 :=
      iisum _ _ _ _ fun j _ => iisum _ _ _ _ fun k _ => ((hint j k).const_mul (w j)).mul_const (w k)
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one
      (((K_cont v t).intervalIntegrable _ _).const_mul _) (Kint v t _ hQ)
    filter_upwards [hM] with s hs
    rw [mul_comm (β * _) ((v:ℝ) * _)]
    exact mul_le_mul_of_nonneg_left (hs.2 w) (K_nonneg v t s)

end TVSDP.PolyOpt.Aux


namespace TVSDP.PolyOpt.Aux

lemma qf_avg0 {m : ℕ} (v : ℕ) (t : ℝ)
    (M : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hint : ∀ j k, IntervalIntegrable (fun s => M s j k) volume 0 1)
    (hM : ∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) 1)), QF (M s) 0) :
    QF (Matrix.of fun j k => ∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * M s j k) 0 := by
  have hM' : ∀ᵐ s ∂volume, s ∈ Icc (0:ℝ) 1 → QF (M s) 0 := (ae_restrict_iff' measurableSet_Icc).mp hM
  refine ⟨fun j k => ?_, fun w => ?_⟩
  · simp only [Matrix.of_apply]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hM'] with s hs hs'
    rw [uIoc_of_le zero_le_one] at hs'
    rw [(hs ⟨hs'.1.le, hs'.2⟩).1 j k]
  · simp only [Matrix.of_apply, zero_mul]
    have hI : ∀ j k, IntervalIntegrable
        (fun s => (v:ℝ) * J (v * (t - s)) * (w j * M s j k * w k)) volume 0 1 := by
      intro j k
      exact Kint v t _ (((hint j k).const_mul (w j)).mul_const (w k))
    have e : ∑ j, ∑ k, w j * (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * M s j k) * w k
        = ∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (∑ j, ∑ k, w j * M s j k * w k) := by
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum (fun j _ => iisum _ _ _ _ fun k _ => hI j k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun k _ => hI j k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
      congr 1; ext s; ring
    rw [e]
    apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
    filter_upwards [hM] with s hs
    have := hs.2 w
    simp only [zero_mul] at this
    exact mul_nonneg (K_nonneg v t s) this

end TVSDP.PolyOpt.Aux

open TVSDP.PolyOpt MeasureTheory

theorem solution {m : ℕ} (M : ℝ → Matrix (Fin m) (Fin m) ℝ) (hM : M ∈ Sm m)
    (hmeas : ∀ j k, Measurable fun s => M s j k)
    (hpsd : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)), (M t).PosSemidef) (v : ℕ) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, (MvMat v M t).PosSemidef := by
  intro t _
  obtain ⟨-, B, hB⟩ := hM
  have hint : ∀ j k, IntervalIntegrable (fun s => M s j k) volume 0 1 :=
    fun j k => mol_intOn _ (hmeas j k) B (fun s hs => hB s hs j k)
  have hq : ∀ᵐ s ∂(volume.restrict (Set.Icc (0:ℝ) 1)), TVSDP.PolyOpt.Aux.QF (M s) 0 := by
    filter_upwards [hpsd] with s hs
    exact (TVSDP.PolyOpt.Aux.qf_iff _ 0).mp (by simpa using hs)
  have := TVSDP.PolyOpt.Aux.qf_avg0 v t M hint hq
  have h2 := (TVSDP.PolyOpt.Aux.qf_iff _ 0).mpr this
  simp only [zero_smul, sub_zero] at h2
  convert h2 using 1
  ext j k
  simp only [MvMat, Mv, Matrix.of_apply]
