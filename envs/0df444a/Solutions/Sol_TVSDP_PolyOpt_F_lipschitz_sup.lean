-- Prove2me | solution 1 for TVSDP.PolyOpt.F_lipschitz_sup
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:21:55.790825+00:00
-- url     : https://prove2.me/submissions/f0e935b7-9218-474f-bed3-21e73840a0d2

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


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

lemma bound_fin {ι X : Type*} [Fintype ι] [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (g : ι → X → ℝ) (hg : ∀ i, ContinuousOn (g i) K) :
    ∃ B, 0 ≤ B ∧ ∀ i, ∀ x ∈ K, |g i x| ≤ B := by
  classical
  have := fun i => hK.exists_bound_of_continuousOn (hg i)
  choose C hC using this
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x hx => ?_⟩
  have h1 : |g i x| ≤ C i := by simpa [Real.norm_eq_abs] using hC i x hx
  have h2 : |C i| ≤ ∑ i, |C i| :=
    Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  linarith [le_abs_self (C i)]

variable {n m : ℕ}

lemma evalMat_apply (A : Matrix (Fin m) (Fin m) (Polynomial ℝ)) (t : ℝ) (j k : Fin m) :
    evalMat A t j k = (A j k).eval t := rfl

lemma evalMat₂_apply (D : Matrix (Fin m) (Fin m) (MvPolynomial (Fin 2) ℝ)) (t s : ℝ) (j k : Fin m) :
    evalMat₂ D t s j k = MvPolynomial.eval ![t, s] (D j k) := rfl

lemma A_cont (A : Matrix (Fin m) (Fin m) (Polynomial ℝ)) (j k : Fin m) :
    Continuous fun t => evalMat A t j k := (A j k).continuous

lemma D_cont (D : Matrix (Fin m) (Fin m) (MvPolynomial (Fin 2) ℝ)) (j k : Fin m) :
    Continuous fun q : ℝ × ℝ => evalMat₂ D q.1 q.2 j k := by
  have : Continuous fun q : ℝ × ℝ => (![q.1, q.2] : Fin 2 → ℝ) := by
    exact continuous_fst.matrixVecCons (continuous_snd.matrixVecCons continuous_const)
  exact (MvPolynomial.continuous_eval (D j k)).comp this

lemma D_cont_s (D : Matrix (Fin m) (Fin m) (MvPolynomial (Fin 2) ℝ)) (j k : Fin m) (t : ℝ) :
    Continuous fun s => evalMat₂ D t s j k := by
  simp only [evalMat₂_apply]
  exact (MvPolynomial.continuous_eval (D j k)).comp
    (continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const))

lemma F_symm (P : Data n m) (u : ℝ → Fin n → ℝ) (t : ℝ) (j k : Fin m) :
    F P u t j k = F P u t k j := by
  have hA : ∀ i j k, P.A i j k = P.A i k j := fun i j k => by
    have := congrFun (congrFun (P.A_symm i) k) j
    simpa [Matrix.transpose_apply] using this
  have hD : ∀ i j k, P.D i j k = P.D i k j := fun i j k => by
    have := congrFun (congrFun (P.D_symm i) k) j
    simpa [Matrix.transpose_apply] using this
  simp only [F, Matrix.of_apply, evalMat_apply, evalMat₂_apply, hA _ j k, hD _ j k]

lemma ii_sub (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable f volume 0 t := by
  apply hf.mono_set
  rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
  exact Icc_subset_Icc le_rfl ht.2

lemma ii_D (P : Data n m) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (i : Fin n)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j k : Fin m) :
    IntervalIntegrable (fun s => f s * evalMat₂ (P.D i) t s j k) volume 0 t :=
  (ii_sub f hf t ht).mul_continuousOn (D_cont_s _ j k t).continuousOn

lemma F_diff (P : Data n m) (u w : ℝ → Fin n → ℝ)
    (hu : ∀ i, IntervalIntegrable (fun s => u s i) volume 0 1)
    (hw : ∀ i, IntervalIntegrable (fun s => w s i) volume 0 1)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j k : Fin m) :
    F P u t j k - F P w t j k = ∑ i, (u t i - w t i) * evalMat (P.A i.succ) t j k
      + ∑ i, ∫ s in (0:ℝ)..t, (u s i - w s i) * evalMat₂ (P.D i) t s j k := by
  have e : ∀ i, ∫ s in (0:ℝ)..t, (u s i - w s i) * evalMat₂ (P.D i) t s j k
      = (∫ s in (0:ℝ)..t, u s i * evalMat₂ (P.D i) t s j k)
        - ∫ s in (0:ℝ)..t, w s i * evalMat₂ (P.D i) t s j k := by
    intro i
    rw [← intervalIntegral.integral_sub (ii_D P _ (hu i) i t ht j k) (ii_D P _ (hw i) i t ht j k)]
    congr 1; ext s; ring
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  simp only [F, Matrix.of_apply, Finset.sum_sub_distrib, sub_mul]
  ring

lemma int_bound (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (hg : Continuous g)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (B : ℝ) (hB : ∀ s ∈ Icc (0:ℝ) 1, |g s| ≤ B) :
    |∫ s in (0:ℝ)..t, f s * g s| ≤ B * ∫ s in (0:ℝ)..1, |f s| := by
  have hft := ii_sub f hf t ht
  refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
  have h1 : ∫ s in (0:ℝ)..t, |f s * g s| ≤ ∫ s in (0:ℝ)..t, B * |f s| := by
    apply intervalIntegral.integral_mono_on ht.1 (hft.mul_continuousOn hg.continuousOn).abs
      (hft.abs.const_mul B)
    intro s hs
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _)
  have h2 : ∫ s in (0:ℝ)..t, B * |f s| ≤ ∫ s in (0:ℝ)..1, B * |f s| := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun s => mul_nonneg hB0 (abs_nonneg _)) (hf.abs.const_mul B)
  simp only [intervalIntegral.integral_const_mul] at h1 h2
  linarith

lemma F_diff_bound (P : Data n m) (u w : ℝ → Fin n → ℝ)
    (hu : ∀ i, IntervalIntegrable (fun s => u s i) volume 0 1)
    (hw : ∀ i, IntervalIntegrable (fun s => w s i) volume 0 1)
    (BD : ℝ) (hBD : ∀ i j k, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, |evalMat₂ (P.D i) t s j k| ≤ BD)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j k : Fin m) :
    |F P u t j k - F P w t j k - ∑ i, (u t i - w t i) * evalMat (P.A i.succ) t j k|
      ≤ BD * ∑ i, ∫ s in (0:ℝ)..1, |u s i - w s i| := by
  rw [F_diff P u w hu hw t ht j k, add_sub_cancel_left, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact int_bound (fun s => u s i - w s i) _ ((hu i).sub (hw i)) (D_cont_s _ j k t) t ht BD
    (fun s hs => hBD i j k t ht s hs)

lemma obj_diff (P : Data n m) (u w : ℝ → Fin n → ℝ)
    (hu : ∀ i, IntervalIntegrable (fun s => u s i) volume 0 1)
    (hw : ∀ i, IntervalIntegrable (fun s => w s i) volume 0 1)
    (Bc : ℝ) (hBc : ∀ i, ∀ t ∈ Icc (0:ℝ) 1, |(P.c i).eval t| ≤ Bc) :
    |obj P u - obj P w| ≤ Bc * ∑ i, ∫ s in (0:ℝ)..1, |u s i - w s i| := by
  have hi : ∀ (x : ℝ → Fin n → ℝ), (∀ i, IntervalIntegrable (fun s => x s i) volume 0 1) →
      ∀ i, IntervalIntegrable (fun t => (P.c i).eval t * x t i) volume 0 1 :=
    fun x hx i => (hx i).continuousOn_mul (P.c i).continuous.continuousOn
  unfold obj
  rw [← intervalIntegral.integral_sub (iisum _ _ _ _ fun i _ => hi u hu i)
    (iisum _ _ _ _ fun i _ => hi w hw i)]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  have hd : ∀ i, IntervalIntegrable (fun s => |u s i - w s i|) volume 0 1 :=
    fun i => ((hu i).sub (hw i)).abs
  rw [Finset.mul_sum]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun i _ => (hd i).const_mul Bc]
  apply intervalIntegral.integral_mono_on zero_le_one
    ((iisum _ _ _ _ fun i _ => hi u hu i).sub (iisum _ _ _ _ fun i _ => hi w hw i)).abs
    (iisum _ _ _ _ fun i _ => (hd i).const_mul Bc)
  intro t ht
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hBc i t ht) (abs_nonneg _)

end TVSDP.PolyOpt.Aux


namespace TVSDP.PolyOpt.Aux
variable {n : ℕ}
lemma Ln_bound (y : ℝ → Fin n → ℝ) (hy : y ∈ Ln n) :
    ∃ γ, 0 ≤ γ ∧ ∀ i, ∀ s ∈ Icc (0:ℝ) 1, |y s i| ≤ γ := by
  obtain ⟨_, M, hM⟩ := hy
  refine ⟨max M 0, le_max_right _ _, fun i s hs => ?_⟩
  have := (norm_le_pi_norm (y s) i).trans (hM s hs)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma Ln_ii (x : ℝ → Fin n → ℝ) (hx : x ∈ Ln n) (i : Fin n) :
    IntervalIntegrable (fun s => x s i) volume 0 1 := by
  obtain ⟨γ, -, hb⟩ := Ln_bound x hx
  exact mol_intOn _ ((measurable_pi_iff.mp hx.1) i) γ (hb i)
end TVSDP.PolyOpt.Aux

open TVSDP.PolyOpt MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup

theorem solution {n m : ℕ} (P : Data n m) (x y : ℝ → Fin n → ℝ)
    (hx : x ∈ Ln n) (hy : y ∈ Ln n) (C M : ℝ)
    (hC : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      ∑ i : Fin n, (‖evalMat (P.A i.succ) t‖ + ‖evalMat₂ (P.D i) t s‖) ≤ C)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖x s - y s‖ ≤ M) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ‖F P x t - F P y t‖ ≤ C * M := by
  intro t ht
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hxy : ∀ i, ∀ s ∈ Set.Icc (0:ℝ) 1, |x s i - y s i| ≤ M := fun i s hs => by
    have := (norm_le_pi_norm (x s - y s) i).trans (hM s hs)
    simpa [Real.norm_eq_abs] using this
  have hxi : ∀ i, IntervalIntegrable (fun s => x s i) volume 0 1 := TVSDP.PolyOpt.Aux.Ln_ii x hx
  have hyi : ∀ i, IntervalIntegrable (fun s => y s i) volume 0 1 := TVSDP.PolyOpt.Aux.Ln_ii y hy
  set a := ∑ i : Fin n, ‖evalMat (P.A i.succ) t‖ with ha
  have hCa : ∀ s ∈ Set.Icc (0:ℝ) 1, ∑ i : Fin n, ‖evalMat₂ (P.D i) t s‖ ≤ C - a := by
    intro s hs
    have := hC t ht s hs
    rw [Finset.sum_add_distrib] at this
    linarith
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hCa0 : 0 ≤ C - a := (Finset.sum_nonneg fun i _ => norm_nonneg _).trans
    (hCa 0 ⟨le_rfl, zero_le_one⟩)
  have hDc : ∀ i, Continuous fun s => ‖evalMat₂ (P.D i) t s‖ := fun i =>
    (continuous_pi fun j => continuous_pi fun k => TVSDP.PolyOpt.Aux.D_cont_s _ j k t).norm
  rw [Matrix.norm_le_iff (by nlinarith)]
  intro j k
  rw [Matrix.sub_apply, TVSDP.PolyOpt.Aux.F_diff P x y hxi hyi t ht j k, Real.norm_eq_abs]
  have b1 : |∑ i, (x t i - y t i) * evalMat (P.A i.succ) t j k| ≤ M * a := by
    rw [ha, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul (hxy i t ht) ?_ (abs_nonneg _) hM0
    have := Matrix.norm_entry_le_entrywise_sup_norm (evalMat (P.A i.succ) t) (i := j) (j := k)
    rwa [Real.norm_eq_abs] at this
  have b2 : ∀ i, |∫ s in (0:ℝ)..t, (x s i - y s i) * evalMat₂ (P.D i) t s j k|
      ≤ ∫ s in (0:ℝ)..t, M * ‖evalMat₂ (P.D i) t s‖ := by
    intro i
    refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
    apply intervalIntegral.integral_mono_on ht.1
      (TVSDP.PolyOpt.Aux.ii_D P _ ((hxi i).sub (hyi i)) i t ht j k).abs
      ((hDc i).intervalIntegrable _ _ |>.const_mul M)
    intro s hs
    rw [abs_mul]
    refine mul_le_mul (hxy i s ⟨hs.1, hs.2.trans ht.2⟩) ?_ (abs_nonneg _) hM0
    have := Matrix.norm_entry_le_entrywise_sup_norm (evalMat₂ (P.D i) t s) (i := j) (j := k)
    rwa [Real.norm_eq_abs] at this
  have b3 : ∑ i, ∫ s in (0:ℝ)..t, M * ‖evalMat₂ (P.D i) t s‖ ≤ M * (C - a) := by
    rw [← intervalIntegral.integral_finsetSum fun i _ => (hDc i).intervalIntegrable _ _ |>.const_mul M]
    have h1 : ∫ s in (0:ℝ)..t, ∑ i, M * ‖evalMat₂ (P.D i) t s‖ ≤ ∫ s in (0:ℝ)..t, M * (C - a) := by
      apply intervalIntegral.integral_mono_on ht.1
        (TVSDP.PolyOpt.Aux.iisum _ _ _ _ fun i _ => (hDc i).intervalIntegrable _ _ |>.const_mul M)
        intervalIntegrable_const
      intro s hs
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hCa s ⟨hs.1, hs.2.trans ht.2⟩) hM0
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have : t * (M * (C - a)) ≤ M * (C - a) := by
      have := mul_nonneg hM0 hCa0
      nlinarith [ht.2]
    linarith
  calc |∑ i, (x t i - y t i) * evalMat (P.A i.succ) t j k
        + ∑ i, ∫ s in (0:ℝ)..t, (x s i - y s i) * evalMat₂ (P.D i) t s j k|
      ≤ |∑ i, (x t i - y t i) * evalMat (P.A i.succ) t j k|
        + ∑ i, |∫ s in (0:ℝ)..t, (x s i - y s i) * evalMat₂ (P.D i) t s j k| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ M * a + M * (C - a) := add_le_add b1 ((Finset.sum_le_sum fun i _ => b2 i).trans b3)
    _ = C * M := by ring
