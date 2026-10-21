-- Prove2me | solution 1 for TVSDP.PolyOpt.convex_comb_strictly_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:20:31.749401+00:00
-- url     : https://prove2.me/submissions/b0b9d2a4-9978-422e-a340-e2d293ee4697

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting
import Definitions.Def_TVSDP_PolyOpt_Mollifier
import Theorems.Thm_TVSDP_PolyOpt_proposition_1

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


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

def UC (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ r > 0, ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s - t| < r → |f s - f t| ≤ ε

lemma UC_of_cont (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) : UC f := by
  intro ε hε
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨r, hr, h⟩ := hu ε hε
  refine ⟨r, hr, fun s hs t ht hst => ?_⟩
  have := h s hs t ht (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at this; exact this.le

lemma UC_add (f g : ℝ → ℝ) (hf : UC f) (hg : UC g) : UC (fun s => f s + g s) := by
  intro ε hε
  obtain ⟨r1, hr1, h1⟩ := hf (ε/2) (by linarith)
  obtain ⟨r2, hr2, h2⟩ := hg (ε/2) (by linarith)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun s hs t ht hst => ?_⟩
  have a := h1 s hs t ht (lt_of_lt_of_le hst (min_le_left _ _))
  have b := h2 s hs t ht (lt_of_lt_of_le hst (min_le_right _ _))
  calc |f s + g s - (f t + g t)| = |(f s - f t) + (g s - g t)| := by ring_nf
    _ ≤ |f s - f t| + |g s - g t| := abs_add_le _ _
    _ ≤ ε := by linarith

lemma UC_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, UC (f i)) :
    UC (fun s => ∑ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro ε hε; exact ⟨1, one_pos, fun s _ t _ _ => by simp; linarith⟩
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact UC_add _ _ (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma UC_contOn (f : ℝ → ℝ) (hf : UC f) : ContinuousOn f (Icc 0 1) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨r, hr, h⟩ := hf (ε/2) (by linarith)
  refine ⟨r, hr, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have := h a ha b hb hab
  linarith

/-- The memory term `G(s) = ∫₀ˢ y(u) D(s,u) du` is uniformly continuous on `[0,1]`. -/
lemma UC_G (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (γ : ℝ)
    (hγ : ∀ s ∈ Icc (0:ℝ) 1, |f s| ≤ γ) (d : ℝ × ℝ → ℝ) (hd : Continuous d) :
    UC (fun s => ∫ u in (0:ℝ)..s, f u * d (s, u)) := by
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans (hγ 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨BD, hBD0, hBD⟩ := bound_fin (ι := Unit) (isCompact_Icc.prod isCompact_Icc)
    (fun _ => d) (fun _ => hd.continuousOn)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (s := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) hd.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  intro ε hε
  obtain ⟨r1, hr1, h1⟩ := hu (ε / (2 * (γ + 1))) (by positivity)
  refine ⟨min r1 (ε / (2 * (γ * BD + 1))), lt_min hr1 (by positivity), fun s hs t ht hst => ?_⟩
  have hfs : ∀ s ∈ Icc (0:ℝ) 1, IntervalIntegrable (fun u => f u * d (s, u)) volume 0 s := by
    intro s hs
    have hc : Continuous fun u => d (s, u) := hd.comp (by fun_prop)
    exact (ii_sub f hf s hs).mul_continuousOn hc.continuousOn
  have hft : IntervalIntegrable (fun u => f u * d (s, u)) volume 0 t := by
    have hc : Continuous fun u => d (s, u) := hd.comp (by fun_prop)
    exact (ii_sub f hf t ht).mul_continuousOn hc.continuousOn
  have hts : IntervalIntegrable (fun u => f u * d (s, u)) volume t s :=
    hft.symm.trans (hfs s hs)
  have split : (∫ u in (0:ℝ)..s, f u * d (s, u)) - ∫ u in (0:ℝ)..t, f u * d (t, u)
      = (∫ u in t..s, f u * d (s, u)) + ∫ u in (0:ℝ)..t, f u * (d (s, u) - d (t, u)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hft hts]
    have : ∫ u in (0:ℝ)..t, f u * (d (s, u) - d (t, u))
        = (∫ u in (0:ℝ)..t, f u * d (s, u)) - ∫ u in (0:ℝ)..t, f u * d (t, u) := by
      rw [← intervalIntegral.integral_sub hft (hfs t ht)]
      congr 1; ext u; ring
    rw [this]; ring
  rw [split]
  have uIoc_sub : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → uIoc a b ⊆ Icc (0:ℝ) 1 := by
    intro a b ha hb x hx
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at hx; exact ⟨ha.1.trans hx.1.le, hx.2.trans hb.2⟩
    · rw [uIoc_of_ge hab] at hx; exact ⟨hb.1.trans hx.1.le, hx.2.trans ha.2⟩
  have e1 : |∫ u in t..s, f u * d (s, u)| ≤ γ * BD * |s - t| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s)
      (f := fun u => f u * d (s, u)) (C := γ * BD) (fun u hu => by
        have hu' := uIoc_sub t s ht hs hu
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hγ u hu') (hBD () (s, u) ⟨hs, hu'⟩) (abs_nonneg _) hγ0)
    simpa [Real.norm_eq_abs] using this
  have e2 : |∫ u in (0:ℝ)..t, f u * (d (s, u) - d (t, u))| ≤ γ * (ε / (2 * (γ + 1))) * |t - 0| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun u => f u * (d (s, u) - d (t, u))) (C := γ * (ε / (2 * (γ + 1)))) (fun u hu => by
        have hu' := uIoc_sub 0 t ⟨le_rfl, zero_le_one⟩ ht hu
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul (hγ u hu') ?_ (abs_nonneg _) hγ0
        have := h1 (s, u) ⟨hs, hu'⟩ (t, u) ⟨ht, hu'⟩ (by
          rw [Prod.dist_eq, Real.dist_eq, dist_self]
          simpa using lt_of_lt_of_le hst (min_le_left _ _))
        rw [Real.dist_eq] at this; exact this.le)
    simpa [Real.norm_eq_abs] using this
  have hst2 : |s - t| < ε / (2 * (γ * BD + 1)) := lt_of_lt_of_le hst (min_le_right _ _)
  have ht1 : |t - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
  have b1 : γ * BD * |s - t| ≤ ε / 2 := by
    have hpos : 0 < 2 * (γ * BD + 1) := by positivity
    have : |s - t| * (2 * (γ * BD + 1)) < ε := by rwa [lt_div_iff₀ hpos] at hst2
    nlinarith [abs_nonneg (s - t), mul_nonneg hγ0 hBD0]
  have b2 : γ * (ε / (2 * (γ + 1))) * |t - 0| ≤ ε / 2 := by
    have h3 : γ * (ε / (2 * (γ + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h4 : 0 ≤ γ * (ε / (2 * (γ + 1))) := by positivity
    nlinarith [abs_nonneg (t - 0)]
  calc |(∫ u in t..s, f u * d (s, u)) + ∫ u in (0:ℝ)..t, f u * (d (s, u) - d (t, u))|
      ≤ |∫ u in t..s, f u * d (s, u)| + |∫ u in (0:ℝ)..t, f u * (d (s, u) - d (t, u))| :=
        abs_add_le _ _
    _ ≤ ε := by linarith

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

lemma eventually_large (r : ℝ) (hr : 0 < r) : ∀ᶠ v : ℕ in atTop, 1 ≤ v ∧ 1 / (v:ℝ) < r := by
  filter_upwards [eventually_ge_atTop (⌈1 / r⌉₊ + 1)] with v hv
  have h1 : (1:ℝ) / r < v := by
    have := Nat.le_ceil (1 / r)
    have : ((⌈1 / r⌉₊ + 1 : ℕ) : ℝ) ≤ v := by exact_mod_cast hv
    push_cast at this; linarith
  have hvpos : (0:ℝ) < v := lt_of_le_of_lt (by positivity) h1
  refine ⟨by omega, ?_⟩
  rw [div_lt_iff₀ hvpos]
  rw [div_lt_iff₀ hr] at h1; linarith

lemma K_mul_const_int (v : ℕ) (t c : ℝ) :
    ∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * c = c * ρ v t := by
  rw [ρ_eq, ← intervalIntegral.integral_const_mul]
  congr 1; ext s; ring

lemma avg_UC (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 1) (huc : UC f) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v : ℕ in atTop, ∀ t ∈ Icc (0:ℝ) 1,
      |f t - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * f s) / ρ v t| ≤ ε := by
  obtain ⟨r, hr, h⟩ := huc ε hε
  filter_upwards [eventually_large r hr] with v ⟨hv, hvr⟩ t ht
  have hρ := ρ_pos v hv t ht
  have e : f t - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * f s) / ρ v t
      = (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (f t - f s)) / ρ v t := by
    rw [eq_div_iff hρ.ne', sub_mul, div_mul_cancel₀ _ hρ.ne', ← K_mul_const_int,
      ← intervalIntegral.integral_sub (Kint v t _ intervalIntegrable_const) (Kint v t _ hf)]
    congr 1; ext s; ring
  rw [e, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  exact kbound v hv t _ (intervalIntegrable_const.sub hf) ε
    (fun s hs hts => h t ht s hs (lt_trans hts hvr))

lemma avg_mul (g a : ℝ → ℝ) (hg : IntervalIntegrable g volume 0 1) (γ : ℝ)
    (hγ : ∀ s ∈ Icc (0:ℝ) 1, |g s| ≤ γ) (ha : Continuous a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v : ℕ in atTop, ∀ t ∈ Icc (0:ℝ) 1,
      |(∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * g s) / ρ v t * a t
        - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (g s * a s)) / ρ v t| ≤ ε := by
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans (hγ 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨r, hr, h⟩ := UC_of_cont a ha.continuousOn (ε / (γ + 1)) (by positivity)
  filter_upwards [eventually_large r hr] with v ⟨hv, hvr⟩ t ht
  have hρ := ρ_pos v hv t ht
  have hga : IntervalIntegrable (fun s => g s * a s) volume 0 1 :=
    hg.mul_continuousOn ha.continuousOn
  have e : (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * g s) / ρ v t * a t
        - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (g s * a s)) / ρ v t
      = (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (g s * (a t - a s))) / ρ v t := by
    rw [div_mul_eq_mul_div, ← sub_div, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub ((Kint v t _ hg).mul_const _) (Kint v t _ hga)]
    congr 1; congr 1; ext s; ring
  rw [e, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine (kbound v hv t _ (hg.mul_continuousOn (continuousOn_const.sub ha.continuousOn))
    (γ * (ε / (γ + 1))) (fun s hs hts => ?_)).trans ?_
  · rw [abs_mul]
    exact mul_le_mul (hγ s hs) (h t ht s hs (lt_trans hts hvr)) (abs_nonneg _) hγ0
  · apply mul_le_mul_of_nonneg_right _ hρ.le
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith

lemma L1_conv (f : ℝ → ℝ) (hf : Measurable f) (γ : ℝ) (hγ : ∀ s ∈ Icc (0:ℝ) 1, |f s| ≤ γ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ v : ℕ in atTop, ∫ s in (0:ℝ)..1, |Mv v f s / ρ v s - f s| ≤ τ := by
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans (hγ 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨hc, ht⟩ := proposition_1 f hf ⟨γ, hγ⟩
  obtain ⟨hc1, ht1⟩ := proposition_1 (fun _ => (1:ℝ)) measurable_const ⟨1, fun _ _ => by simp⟩
  set c0 := cJ * Real.exp (-2) / 2 with hc0
  have hc0pos : 0 < c0 := by have := cJ_pos; positivity
  have hT : Tendsto (fun v : ℕ => ((∫ s in (0:ℝ)..1, |Mv v f s - f s|)
      + γ * ∫ s in (0:ℝ)..1, |Mv v (fun _ => (1:ℝ)) s - 1|) / c0) atTop (𝓝 0) := by
    have := (ht.add (ht1.const_mul γ)).div_const c0
    simpa using this
  have hev := (hT.eventually (gt_mem_nhds hτ))
  filter_upwards [hev, eventually_ge_atTop 1] with v hv hv1
  have hfi : IntervalIntegrable f volume 0 1 := mol_intOn f hf γ hγ
  have hρc : Continuous (ρ v) := hc1 v
  have hq : ContinuousOn (fun s => Mv v f s / ρ v s) (Icc 0 1) :=
    (hc v).continuousOn.div hρc.continuousOn (fun s hs => (ρ_pos v hv1 s hs).ne')
  have hqi : IntervalIntegrable (fun s => Mv v f s / ρ v s) volume 0 1 :=
    hq.intervalIntegrable_of_Icc zero_le_one
  have i1 : IntervalIntegrable (fun s => |Mv v f s - f s|) volume 0 1 :=
    (((hc v).intervalIntegrable _ _).sub hfi).abs
  have i2 : IntervalIntegrable (fun s => |Mv v (fun _ => (1:ℝ)) s - 1|) volume 0 1 :=
    (((hc1 v).intervalIntegrable _ _).sub intervalIntegrable_const).abs
  refine le_trans ?_ hv.le
  have : ((∫ s in (0:ℝ)..1, |Mv v f s - f s|)
      + γ * ∫ s in (0:ℝ)..1, |Mv v (fun _ => (1:ℝ)) s - 1|) / c0
      = ∫ s in (0:ℝ)..1, (|Mv v f s - f s| + γ * |Mv v (fun _ => (1:ℝ)) s - 1|) / c0 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add i1 (i2.const_mul γ),
      intervalIntegral.integral_const_mul]
  rw [this]
  apply intervalIntegral.integral_mono_on zero_le_one (hqi.sub hfi).abs
    ((i1.add (i2.const_mul γ)).div_const c0)
  intro s hs
  have hρ := ρ_pos v hv1 s hs
  have hρl := ρ_lower v hv1 s hs
  have e : Mv v f s / ρ v s - f s = ((Mv v f s - f s) + f s * (1 - ρ v s)) / ρ v s := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hρ]
  have hn : |(Mv v f s - f s) + f s * (1 - ρ v s)| ≤ |Mv v f s - f s| + γ * |Mv v (fun _ => (1:ℝ)) s - 1| := by
    refine (abs_add_le _ _).trans ?_
    have : |f s * (1 - ρ v s)| ≤ γ * |Mv v (fun _ => (1:ℝ)) s - 1| := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (hγ s hs) (abs_nonneg _)
    linarith
  calc |(Mv v f s - f s) + f s * (1 - ρ v s)| / ρ v s
      ≤ (|Mv v f s - f s| + γ * |Mv v (fun _ => (1:ℝ)) s - 1|) / ρ v s :=
        div_le_div_of_nonneg_right hn hρ.le
    _ ≤ (|Mv v f s - f s| + γ * |Mv v (fun _ => (1:ℝ)) s - 1|) / c0 :=
        div_le_div_of_nonneg_left (by positivity) hc0pos hρl

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

variable {n m : ℕ}

lemma arith (a b τ X : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 ≤ τ)
    (h : τ ≤ X / ((a + 1) * (b + 1))) : a * (b * τ) ≤ X := by
  have hpos : 0 < (a + 1) * (b + 1) := by positivity
  rw [le_div_iff₀ hpos] at h
  nlinarith [mul_nonneg (by linarith : 0 ≤ a + b + 1) hτ]

lemma sum_le_n (f : Fin n → ℝ) (θ : ℝ) (h : ∀ i, f i ≤ θ) : ∑ i, f i ≤ n * θ := by
  calc ∑ i, f i ≤ ∑ _i : Fin n, θ := Finset.sum_le_sum fun i _ => h i
    _ = n * θ := by simp

lemma bounds (P : Data n m) : ∃ BA BD Bc : ℝ, 0 ≤ BA ∧ 0 ≤ BD ∧ 0 ≤ Bc ∧
    (∀ i : Fin (n+1), ∀ j k, ∀ t ∈ Icc (0:ℝ) 1, |evalMat (P.A i) t j k| ≤ BA) ∧
    (∀ i j k, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, |evalMat₂ (P.D i) t s j k| ≤ BD) ∧
    (∀ i, ∀ t ∈ Icc (0:ℝ) 1, |(P.c i).eval t| ≤ Bc) := by
  obtain ⟨BA, hBA0, hBA⟩ := bound_fin (ι := Fin (n+1) × Fin m × Fin m) (isCompact_Icc (a := (0:ℝ)) (b := 1))
    (fun q t => evalMat (P.A q.1) t q.2.1 q.2.2) (fun q => (A_cont _ _ _).continuousOn)
  obtain ⟨BD, hBD0, hBD⟩ := bound_fin (ι := Fin n × Fin m × Fin m)
    ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod (isCompact_Icc (a := (0:ℝ)) (b := 1)))
    (fun q x => evalMat₂ (P.D q.1) x.1 x.2 q.2.1 q.2.2) (fun q => (D_cont _ _ _).continuousOn)
  obtain ⟨Bc, hBc0, hBc⟩ := bound_fin (ι := Fin n) (isCompact_Icc (a := (0:ℝ)) (b := 1))
    (fun i t => (P.c i).eval t) (fun i => (P.c i).continuous.continuousOn)
  exact ⟨BA, BD, Bc, hBA0, hBD0, hBc0, fun i j k t ht => hBA (i, j, k) t ht,
    fun i j k t ht s hs => hBD (i, j, k) (t, s) ⟨ht, hs⟩, hBc⟩

lemma stepP (P : Data n m) (z : ℝ → Fin n → ℝ)
    (hz : ∀ i, ContinuousOn (fun s => z s i) (Icc 0 1)) (β : ℝ) (hβ : 0 < β)
    (hzq : ∀ t ∈ Icc (0:ℝ) 1, QF (F P z t) β) (η : ℝ) (hη : 0 < η) :
    ∃ p : Fin n → Polynomial ℝ, (∀ t ∈ Icc (0:ℝ) 1, QF (F P (polySol p) t) (β / 2)) ∧
      |obj P (polySol p) - obj P z| ≤ η := by
  obtain ⟨BA, BD, Bc, hBA0, hBD0, hBc0, hBA, hBD, hBc⟩ := bounds P
  set θ := min ((β / 2) / (((m:ℝ) + 1) * ((n:ℝ) * (BA + BD) + 1))) (η / ((Bc + 1) * ((n:ℝ) + 1)))
    with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  choose p hp using fun i => exists_polynomial_near_of_continuousOn 0 1 _ (hz i) θ hθ
  refine ⟨p, fun t ht => ?_, ?_⟩
  · have hpi : ∀ i, IntervalIntegrable (fun s => polySol p s i) volume 0 1 :=
      fun i => (p i).continuous.intervalIntegrable _ _
    have hzi : ∀ i, IntervalIntegrable (fun s => z s i) volume 0 1 :=
      fun i => (hz i).intervalIntegrable_of_Icc zero_le_one
    have hI1 : ∀ i, ∫ s in (0:ℝ)..1, |polySol p s i - z s i| ≤ θ := by
      intro i
      have := intervalIntegral.integral_mono_on zero_le_one ((hpi i).sub (hzi i)).abs
        (intervalIntegrable_const (c := θ)) (fun s hs => (hp i s hs).le)
      simpa using this
    apply qf_perturb (F P z t) (F P (polySol p) t) β ((n:ℝ) * (BA + BD) * θ) (hzq t ht)
      (F_symm P _ t) _ (by positivity)
    · have := arith m ((n:ℝ) * (BA + BD)) θ (β / 2) (by positivity) (by positivity) hθ.le
        (min_le_left _ _)
      linarith [show (m:ℝ) * ((n:ℝ) * (BA + BD) * θ) = (m:ℝ) * (((n:ℝ) * (BA + BD)) * θ) by ring]
    · intro j k
      have h1 := F_diff_bound P (polySol p) z hpi hzi BD hBD t ht j k
      have h2 : |∑ i, (polySol p t i - z t i) * evalMat (P.A i.succ) t j k| ≤ n * (θ * BA) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_n _ _ fun i => ?_)
        rw [abs_mul]
        exact mul_le_mul (hp i t ht).le (hBA _ j k t ht) (abs_nonneg _) hθ.le
      have h3 : BD * ∑ i, ∫ s in (0:ℝ)..1, |polySol p s i - z s i| ≤ BD * (n * θ) :=
        mul_le_mul_of_nonneg_left (sum_le_n _ _ hI1) hBD0
      have := abs_sub_abs_le_abs_sub (F P (polySol p) t j k - F P z t j k)
        (∑ i, (polySol p t i - z t i) * evalMat (P.A i.succ) t j k)
      have e : (n:ℝ) * (BA + BD) * θ = n * (θ * BA) + BD * (n * θ) := by ring
      rw [e]; linarith
  · have hpi : ∀ i, IntervalIntegrable (fun s => polySol p s i) volume 0 1 :=
      fun i => (p i).continuous.intervalIntegrable _ _
    have hzi : ∀ i, IntervalIntegrable (fun s => z s i) volume 0 1 :=
      fun i => (hz i).intervalIntegrable_of_Icc zero_le_one
    have hI1 : ∀ i, ∫ s in (0:ℝ)..1, |polySol p s i - z s i| ≤ θ := by
      intro i
      have := intervalIntegral.integral_mono_on zero_le_one ((hpi i).sub (hzi i)).abs
        (intervalIntegrable_const (c := θ)) (fun s hs => (hp i s hs).le)
      simpa using this
    refine (obj_diff P _ z hpi hzi Bc hBc).trans ?_
    refine (mul_le_mul_of_nonneg_left (sum_le_n _ _ hI1) hBc0).trans ?_
    exact arith Bc n θ η hBc0 (by positivity) hθ.le (min_le_right _ _)

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

variable {n m : ℕ}

lemma Ln_bound (y : ℝ → Fin n → ℝ) (hy : y ∈ Ln n) :
    ∃ γ, 0 ≤ γ ∧ ∀ i, ∀ s ∈ Icc (0:ℝ) 1, |y s i| ≤ γ := by
  obtain ⟨_, M, hM⟩ := hy
  refine ⟨max M 0, le_max_right _ _, fun i s hs => ?_⟩
  have := (norm_le_pi_norm (y s) i).trans (hM s hs)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma stepS (P : Data n m) (y : ℝ → Fin n → ℝ) (hy : y ∈ Ln n) (δ : ℝ) (hδ : 0 < δ)
    (hyq : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), QF (F P y t) δ) (η : ℝ) (hη : 0 < η) :
    ∃ z : ℝ → Fin n → ℝ, (∀ i, ContinuousOn (fun s => z s i) (Icc 0 1)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, QF (F P z t) (δ / 2)) ∧ |obj P z - obj P y| ≤ η := by
  obtain ⟨BA, BD, Bc, hBA0, hBD0, hBc0, hBA, hBD, hBc⟩ := bounds P
  obtain ⟨γ, hγ0, hyb⟩ := Ln_bound y hy
  have hymi : ∀ i, Measurable fun s => y s i := fun i => (measurable_pi_iff.mp hy.1) i
  have hyi : ∀ i, IntervalIntegrable (fun s => y s i) volume 0 1 :=
    fun i => mol_intOn _ (hymi i) γ (hyb i)
  set Φ : Fin m → Fin m → ℝ → ℝ := fun j k s =>
    evalMat (P.A 0) s j k + ∑ i, ∫ u in (0:ℝ)..s, y u i * evalMat₂ (P.D i) s u j k with hΦdef
  have hΦF : ∀ j k s, F P y s j k = Φ j k s + ∑ i, y s i * evalMat (P.A i.succ) s j k := by
    intro j k s; simp only [F, Matrix.of_apply, hΦdef]; ring
  have hΦuc : ∀ j k, UC (Φ j k) := by
    intro j k
    refine UC_add _ _ (UC_of_cont _ (A_cont _ j k).continuousOn)
      (UC_sum _ _ fun i _ => ?_)
    exact UC_G (fun u => y u i) (hyi i) γ (hyb i) (fun q => evalMat₂ (P.D i) q.1 q.2 j k)
      (D_cont _ j k)
  have hΦi : ∀ j k, IntervalIntegrable (Φ j k) volume 0 1 :=
    fun j k => (UC_contOn _ (hΦuc j k)).intervalIntegrable_of_Icc zero_le_one
  set θ' := δ / (2 * ((m:ℝ) + 1)) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  set τ := min ((θ' / 3) / ((BD + 1) * ((n:ℝ) + 1))) (η / ((Bc + 1) * ((n:ℝ) + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
  set ε2 := (θ' / 3) / ((n:ℝ) + 1) with hε2
  have hε20 : 0 < ε2 := by positivity
  have E1 : ∀ᶠ v : ℕ in atTop, ∀ i,
      ∫ s in (0:ℝ)..1, |Mv v (fun u => y u i) s / ρ v s - y s i| ≤ τ :=
    eventually_all.2 fun i => L1_conv _ (hymi i) γ (hyb i) τ hτ0
  have E2 : ∀ᶠ v : ℕ in atTop, ∀ j k, ∀ t ∈ Icc (0:ℝ) 1,
      |Φ j k t - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * Φ j k s) / ρ v t| ≤ θ' / 3 :=
    eventually_all.2 fun j => eventually_all.2 fun k =>
      avg_UC _ (hΦi j k) (hΦuc j k) _ (by positivity)
  have E3 : ∀ᶠ v : ℕ in atTop, ∀ i j k, ∀ t ∈ Icc (0:ℝ) 1,
      |(∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * y s i) / ρ v t * evalMat (P.A i.succ) t j k
        - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * (y s i * evalMat (P.A i.succ) s j k))
          / ρ v t| ≤ ε2 :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      avg_mul _ _ (hyi i) γ (hyb i) (A_cont _ j k) ε2 hε20
  obtain ⟨v, hv1, hE1, hE2, hE3⟩ := ((eventually_ge_atTop 1).and (E1.and (E2.and E3))).exists
  obtain ⟨hcont, -⟩ := proposition_1 (fun _ => (1:ℝ)) measurable_const ⟨1, fun _ _ => by simp⟩
  set z : ℝ → Fin n → ℝ := fun s i => Mv v (fun u => y u i) s / ρ v s with hzdef
  have hzc : ∀ i, ContinuousOn (fun s => z s i) (Icc 0 1) := fun i =>
    ((proposition_1 _ (hymi i) ⟨γ, hyb i⟩).1 v).continuousOn.div (hcont v).continuousOn
      (fun s hs => (ρ_pos v hv1 s hs).ne')
  have hzi : ∀ i, IntervalIntegrable (fun s => z s i) volume 0 1 :=
    fun i => (hzc i).intervalIntegrable_of_Icc zero_le_one
  have hI1 : BD * ∑ i, ∫ s in (0:ℝ)..1, |z s i - y s i| ≤ θ' / 3 :=
    (mul_le_mul_of_nonneg_left (sum_le_n _ _ hE1) hBD0).trans
      (arith BD n τ (θ' / 3) hBD0 (by positivity) hτ0.le (min_le_left _ _))
  refine ⟨z, hzc, fun t ht => ?_, ?_⟩
  · have hρ := ρ_pos v hv1 t ht
    have hyA : ∀ i j k, IntervalIntegrable (fun s => y s i * evalMat (P.A i.succ) s j k) volume 0 1 :=
      fun i j k => (hyi i).mul_continuousOn (A_cont _ j k).continuousOn
    have hFi : ∀ j k, IntervalIntegrable (fun s => F P y s j k) volume 0 1 := by
      intro j k
      simp only [hΦF]
      exact (hΦi j k).add (iisum _ _ _ _ fun i _ => hyA i j k)
    have hN := qf_avg v hv1 t ht (F P y) hFi δ hyq
    refine qf_perturb _ (F P z t) δ θ' hN (F_symm P z t) (fun j k => ?_) hθ'0.le ?_
    · simp only [Matrix.of_apply]
      have hsplit : (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * F P y s j k) / ρ v t
          = (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * Φ j k s) / ρ v t
            + ∑ i, (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) *
                (y s i * evalMat (P.A i.succ) s j k)) / ρ v t := by
        rw [← Finset.sum_div, ← add_div]
        congr 1
        rw [← intervalIntegral.integral_finsetSum fun i _ => Kint v t _ (hyA i j k),
          ← intervalIntegral.integral_add (Kint v t _ (hΦi j k))
            (iisum _ _ _ _ fun i _ => Kint v t _ (hyA i j k))]
        congr 1; ext s
        rw [hΦF, mul_add, Finset.mul_sum]
      rw [hsplit]
      have key : F P z t j k - ((∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * Φ j k s) / ρ v t
            + ∑ i, (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) *
                (y s i * evalMat (P.A i.succ) s j k)) / ρ v t)
          = (F P z t j k - F P y t j k - ∑ i, (z t i - y t i) * evalMat (P.A i.succ) t j k)
            + (Φ j k t - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * Φ j k s) / ρ v t)
            + ∑ i, (z t i * evalMat (P.A i.succ) t j k
                - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) *
                  (y s i * evalMat (P.A i.succ) s j k)) / ρ v t) := by
        rw [hΦF j k t]
        simp only [Finset.sum_sub_distrib, sub_mul]
        ring
      rw [key]
      have b1 := F_diff_bound P z y hzi hyi BD hBD t ht j k
      have b2 := hE2 j k t ht
      have b3 : |∑ i, (z t i * evalMat (P.A i.succ) t j k
                - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) *
                  (y s i * evalMat (P.A i.succ) s j k)) / ρ v t)| ≤ n * ε2 :=
        (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_n _ _ fun i => hE3 i j k t ht)
      have b4 : (n:ℝ) * ε2 ≤ θ' / 3 := by
        rw [hε2, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      calc _ ≤ |F P z t j k - F P y t j k - ∑ i, (z t i - y t i) * evalMat (P.A i.succ) t j k|
            + |Φ j k t - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) * Φ j k s) / ρ v t|
            + |∑ i, (z t i * evalMat (P.A i.succ) t j k
                - (∫ s in (0:ℝ)..1, (v:ℝ) * J (v * (t - s)) *
                  (y s i * evalMat (P.A i.succ) s j k)) / ρ v t)| := abs_add_three _ _ _
        _ ≤ θ' := by linarith
    · rw [hθ', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
  · refine (obj_diff P z y hzi hyi Bc hBc).trans ?_
    refine (mul_le_mul_of_nonneg_left (sum_le_n _ _ hE1) hBc0).trans ?_
    exact arith Bc n τ η hBc0 (by positivity) hτ0.le (min_le_right _ _)

end TVSDP.PolyOpt.Aux


set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

namespace TVSDP.PolyOpt.Aux

variable {n m : ℕ}

lemma qf_mono {M : Matrix (Fin m) (Fin m) ℝ} {β β' : ℝ} (h : QF M β) (hb : β' ≤ β) : QF M β' := by
  refine ⟨h.1, fun w => le_trans ?_ (h.2 w)⟩
  exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma qf_zero_psd {M : Matrix (Fin m) (Fin m) ℝ} (h : QF M 0) : M.PosSemidef := by
  have := (qf_iff M 0).mpr h
  simpa using this

lemma polySol_Ln (p : Fin n → Polynomial ℝ) : polySol p ∈ Ln n := by
  refine ⟨measurable_pi_lambda _ fun i => (p i).continuous.measurable, ?_⟩
  obtain ⟨B, hB0, hB⟩ := bound_fin (ι := Fin n) (isCompact_Icc (a := (0:ℝ)) (b := 1))
    (fun i t => (p i).eval t) (fun i => (p i).continuous.continuousOn)
  refine ⟨B, fun t ht => (pi_norm_le_iff_of_nonneg hB0).mpr fun i => ?_⟩
  rw [Real.norm_eq_abs]; exact hB i t ht

lemma core (P : Data n m) (y : ℝ → Fin n → ℝ) (hy : y ∈ Ln n) (δ : ℝ) (hδ : 0 < δ)
    (hyq : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), QF (F P y t) δ) (η : ℝ) (hη : 0 < η) :
    ∃ p : Fin n → Polynomial ℝ, Feasible P (polySol p) ∧ |obj P (polySol p) - obj P y| ≤ η := by
  obtain ⟨z, hzc, hzq, hzo⟩ := stepS P y hy δ hδ hyq (η / 2) (by linarith)
  obtain ⟨p, hpq, hpo⟩ := stepP P z hzc (δ / 2) (by linarith) hzq (η / 2) (by linarith)
  refine ⟨p, ⟨polySol_Ln p, ?_⟩, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun t ht => qf_zero_psd (qf_mono (hpq t ht) (by linarith))
  · calc |obj P (polySol p) - obj P y| = |(obj P (polySol p) - obj P z) + (obj P z - obj P y)| := by
          ring_nf
      _ ≤ |obj P (polySol p) - obj P z| + |obj P z - obj P y| := abs_add_le _ _
      _ ≤ η := by linarith

lemma Ln_ii (x : ℝ → Fin n → ℝ) (hx : x ∈ Ln n) (i : Fin n) :
    IntervalIntegrable (fun s => x s i) volume 0 1 := by
  obtain ⟨γ, -, hb⟩ := Ln_bound x hx
  exact mol_intOn _ ((measurable_pi_iff.mp hx.1) i) γ (hb i)

lemma convex_F (P : Data n m) (x xs : ℝ → Fin n → ℝ) (hx : x ∈ Ln n) (hxs : xs ∈ Ln n)
    (a b : ℝ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j k : Fin m) (hab : a + b = 1) :
    F P (a • x + b • xs) t j k = a * F P x t j k + b * F P xs t j k := by
  have e : ∀ i, ∫ s in (0:ℝ)..t, (a • x + b • xs) s i * evalMat₂ (P.D i) t s j k
      = a * (∫ s in (0:ℝ)..t, x s i * evalMat₂ (P.D i) t s j k)
        + b * ∫ s in (0:ℝ)..t, xs s i * evalMat₂ (P.D i) t s j k := by
    intro i
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((ii_D P _ (Ln_ii x hx i) i t ht j k).const_mul a)
        ((ii_D P _ (Ln_ii xs hxs i) i t ht j k).const_mul b)]
    congr 1; ext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hs : ∀ i, (a • x + b • xs) t i = a * x t i + b * xs t i := fun i => rfl
  simp only [F, Matrix.of_apply]
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [hs]
  have h1 : ∑ i, (a * x t i + b * xs t i) * evalMat (P.A i.succ) t j k
      = a * ∑ i, x t i * evalMat (P.A i.succ) t j k + b * ∑ i, xs t i * evalMat (P.A i.succ) t j k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (a * (∫ s in (0:ℝ)..t, x s i * evalMat₂ (P.D i) t s j k)
        + b * ∫ s in (0:ℝ)..t, xs s i * evalMat₂ (P.D i) t s j k)
      = a * ∑ i, (∫ s in (0:ℝ)..t, x s i * evalMat₂ (P.D i) t s j k)
        + b * ∑ i, ∫ s in (0:ℝ)..t, xs s i * evalMat₂ (P.D i) t s j k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [h1, h2]
  linear_combination (-(evalMat (P.A 0) t j k)) * hab

lemma convex_obj (P : Data n m) (x xs : ℝ → Fin n → ℝ) (hx : x ∈ Ln n) (hxs : xs ∈ Ln n)
    (a b : ℝ) : obj P (a • x + b • xs) = a * obj P x + b * obj P xs := by
  have hi : ∀ (u : ℝ → Fin n → ℝ), u ∈ Ln n →
      IntervalIntegrable (fun t => ∑ i, (P.c i).eval t * u t i) volume 0 1 :=
    fun u hu => iisum _ _ _ _ fun i _ =>
      (Ln_ii u hu i).continuousOn_mul (P.c i).continuous.continuousOn
  unfold obj
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hi x hx).const_mul a) ((hi xs hxs).const_mul b)]
  congr 1; ext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma convex_Ln (x xs : ℝ → Fin n → ℝ) (hx : x ∈ Ln n) (hxs : xs ∈ Ln n) (a b : ℝ) :
    a • x + b • xs ∈ Ln n := by
  obtain ⟨hxm, Mx, hMx⟩ := hx
  obtain ⟨hsm, Ms, hMs⟩ := hxs
  refine ⟨(hxm.const_smul a).add (hsm.const_smul b), |a| * Mx + |b| * Ms, fun t ht => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact add_le_add (mul_le_mul_of_nonneg_left (hMx t ht) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (hMs t ht) (abs_nonneg _))

lemma convex_qf (P : Data n m) (x xs : ℝ → Fin n → ℝ) (hx : Feasible P x) (hxs : xs ∈ Ln n)
    (ε : ℝ) (hxsε : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)),
      (F P xs t - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (lam : ℝ) (hl : lam ∈ Ioo (0:ℝ) 1) :
    ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), QF (F P ((1 - lam) • x + lam • xs) t) (lam * ε) := by
  have hx' : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), t ∈ Icc (0:ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hx.2, hxsε, hx'] with t h1 h2 ht
  have q1 : QF (F P x t) 0 := (qf_iff _ 0).mp (by simpa using h1)
  have q2 : QF (F P xs t) ε := (qf_iff _ ε).mp h2
  refine ⟨F_symm P _ t, fun w => ?_⟩
  have e : ∑ j, ∑ k, w j * F P ((1 - lam) • x + lam • xs) t j k * w k
      = (1 - lam) * (∑ j, ∑ k, w j * F P x t j k * w k)
        + lam * ∑ j, ∑ k, w j * F P xs t j k * w k := by
    simp only [convex_F P x xs hx.1 hxs (1 - lam) lam t ht _ _ (by ring), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have a1 := q1.2 w
  have a2 := q2.2 w
  have hl1 : 0 ≤ 1 - lam := by linarith [hl.2]
  nlinarith [mul_le_mul_of_nonneg_left a1 hl1, mul_le_mul_of_nonneg_left a2 hl.1.le]

lemma approx (P : Data n m) (hP : StrictlyFeasible P) (x : ℝ → Fin n → ℝ) (hx : Feasible P x)
    (η : ℝ) (hη : 0 < η) :
    ∃ p : Fin n → Polynomial ℝ, Feasible P (polySol p) ∧ obj P x - η ≤ obj P (polySol p) := by
  obtain ⟨xs, hxs, ε, hε, hxsε⟩ := hP
  set d := |obj P xs - obj P x|
  set lam := min (1 / 2) (η / (2 * (d + 1))) with hlam
  have hl0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hl1 : lam < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨p, hpf, hpo⟩ := core P _ (convex_Ln x xs hx.1 hxs (1 - lam) lam) (lam * ε)
    (by positivity) (convex_qf P x xs hx hxs ε hxsε lam ⟨hl0, hl1⟩) (η / 2) (by linarith)
  refine ⟨p, hpf, ?_⟩
  rw [convex_obj P x xs hx.1 hxs] at hpo
  have hld : lam * d ≤ η / 2 := by
    have : lam ≤ η / (2 * (d + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg (obj P xs - obj P x)]
  have h3 : -d ≤ obj P xs - obj P x := neg_abs_le _
  have h4 := (abs_le.mp hpo).1
  nlinarith

theorem main (P : Data n m) (hP : StrictlyFeasible P) :
    ∃ p : ℕ → Fin n → Polynomial ℝ,
      (∀ k, Feasible P (polySol (p k))) ∧
      Tendsto (fun k => ((obj P (polySol (p k)) : ℝ) : EReal)) atTop (𝓝 (opt P)) := by
  set T : Set EReal := {r | ∃ p : Fin n → Polynomial ℝ, Feasible P (polySol p) ∧
    r = ((obj P (polySol p) : ℝ) : EReal)} with hT
  have hxsF : ∃ x, Feasible P x := by
    obtain ⟨xs, hxs, ε, hε, hxsε⟩ := hP
    refine ⟨xs, hxs, ?_⟩
    filter_upwards [hxsε] with t ht
    exact qf_zero_psd (qf_mono ((qf_iff _ ε).mp ht) hε.le)
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hxsF
    obtain ⟨p, hp, -⟩ := approx P hP x hx 1 one_pos
    exact ⟨_, p, hp, rfl⟩
  have hsup : sSup T = opt P := by
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨p, hp, rfl⟩
      exact le_iSup₂_of_le (f := fun (x : ℝ → Fin n → ℝ) (_ : Feasible P x) =>
        ((obj P x : ℝ) : EReal)) (polySol p) hp le_rfl
    · apply iSup₂_le
      intro x hx
      by_contra hlt
      push Not at hlt
      obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have ha2' : a < obj P x := EReal.coe_lt_coe_iff.mp ha2
      obtain ⟨p, hp, hpo⟩ := approx P hP x hx (obj P x - a) (by linarith)
      have : ((obj P (polySol p) : ℝ) : EReal) ≤ sSup T := le_sSup ⟨p, hp, rfl⟩
      have h5 : (a : EReal) ≤ ((obj P (polySol p) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by linarith)
      exact absurd (lt_of_lt_of_le ha1 (h5.trans this)) (lt_irrefl _)
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hTne (OrderTop.bddAbove T)
  choose p hp hpe using hmem
  refine ⟨p, hp, ?_⟩
  rw [← hsup]
  have : (fun k => ((obj P (polySol (p k)) : ℝ) : EReal)) = u := funext fun k => (hpe k).symm
  rw [this]; exact hu

end TVSDP.PolyOpt.Aux


open TVSDP.PolyOpt MeasureTheory Filter Topology

theorem solution {n m : ℕ} (P : Data n m) (x xs : ℝ → Fin n → ℝ)
    (hx : Feasible P x) (hxs : xs ∈ Ln n) (ε : ℝ) (hε : 0 < ε)
    (hxsε : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      (F P xs t - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) :
    (∀ lam ∈ Set.Ioo (0:ℝ) 1,
      (1 - lam) • x + lam • xs ∈ Ln n ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
        (F P ((1 - lam) • x + lam • xs) t
          - (lam * ε) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) ∧
    Tendsto (fun lam : ℝ => obj P ((1 - lam) • x + lam • xs)) (𝓝[>] 0) (𝓝 (obj P x)) := by
  refine ⟨fun lam hl => ⟨TVSDP.PolyOpt.Aux.convex_Ln x xs hx.1 hxs _ _, ?_⟩, ?_⟩
  · filter_upwards [TVSDP.PolyOpt.Aux.convex_qf P x xs hx hxs ε hxsε lam hl] with t ht
    exact (TVSDP.PolyOpt.Aux.qf_iff _ _).mpr ht
  · have e : (fun lam : ℝ => obj P ((1 - lam) • x + lam • xs))
        = fun lam => (1 - lam) * obj P x + lam * obj P xs :=
      funext fun lam => TVSDP.PolyOpt.Aux.convex_obj P x xs hx.1 hxs _ _
    rw [e]
    have hc : Continuous fun lam : ℝ => (1 - lam) * obj P x + lam * obj P xs := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
