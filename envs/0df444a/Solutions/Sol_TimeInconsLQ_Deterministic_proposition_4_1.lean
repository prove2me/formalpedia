-- Prove2me | solution 1 for TimeInconsLQ.Deterministic.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:31:46.508016+00:00
-- url     : https://prove2.me/submissions/85a23077-d10a-43b1-b473-4427c5dac13b

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

open TimeInconsLQ.Deterministic

namespace TILQ2Prop41

lemma rhs49M_eq {l d : ℕ} (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) :
    rhs49M c T s m (m / j) = rhs410M c T s m j := by
  unfold rhs49M rhs410M; ring

lemma alg {l d : ℕ} (c : Coeffs l d) (T s : ℝ≥0) (m j : ℝ) (hm : m ≠ 0) (hj : j ≠ 0) :
    rhs410M c T s m j * j⁻¹ + m * (-(rhs410J c T s m j) / j ^ 2)
      = rhs49N c T s m (m / j) := by
  unfold rhs410M rhs410J rhs49N
  simp only [BDC, mulVec_add, dotProduct_add, add_dotProduct]
  generalize c.B s ⬝ᵥ (Kinv c s m *ᵥ c.B s) = x1
  generalize c.B s ⬝ᵥ (Kinv c s m *ᵥ DtC c s) = x2
  generalize DtC c s ⬝ᵥ (Kinv c s m *ᵥ c.B s) = x3
  generalize DtC c s ⬝ᵥ (Kinv c s m *ᵥ DtC c s) = x4
  field_simp
  ring

lemma inv_sub_bound {x y κ : ℝ} (hκ : 0 < κ) (hx : κ ≤ x) (hy : κ ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| / κ ^ 2 := by
  have hx0 : 0 < x := hκ.trans_le hx
  have hy0 : 0 < y := hκ.trans_le hy
  rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith

lemma ac_inv {f : ℝ → ℝ} {a b κ : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (hκ : 0 < κ)
    (hb : ∀ x ∈ Set.uIcc a b, κ ≤ f x) :
    AbsolutelyContinuousOnInterval (fun x => (f x)⁻¹) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε * κ ^ 2) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have h1 := h E hE hlen
  calc ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1)⁻¹ (f (E.2 i).2)⁻¹
      ≤ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) / κ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k1, k2⟩ := hE.1 i hi
        rw [Real.dist_eq, Real.dist_eq]
        exact inv_sub_bound hκ (hb _ k1) (hb _ k2)
    _ = (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) / κ ^ 2 := by
        rw [Finset.sum_div]
    _ < ε := by rw [div_lt_iff₀ (by positivity)]; exact h1

lemma ac_const_add {F : ℝ → ℝ} {a b : ℝ} (C : ℝ) (hF : AbsolutelyContinuousOnInterval F a b) :
    AbsolutelyContinuousOnInterval (fun x => C + F x) a b :=
  ((LipschitzWith.const (α := ℝ) C).lipschitzOnWith (s := Set.uIcc a b)
    |>.absolutelyContinuousOnInterval).fun_add hF

end TILQ2Prop41

open TILQ2Prop41 in
theorem solution {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0) (M J : ℝ≥0 → ℝ)
    (hMJ : IsPosSol410 c T M J) :
    IsPosSol49 c T M (fun s => M s / J s) := by
  obtain ⟨⟨hU, hiM, hiJ, heq⟩, hpos⟩ := hMJ
  set fM : ℝ → ℝ := fun r => rhs410M c T r.toNNReal (M r.toNNReal) (J r.toNNReal) with hfM
  set fJ : ℝ → ℝ := fun r => rhs410J c T r.toNNReal (M r.toNNReal) (J r.toNNReal) with hfJ
  have hT0 : (0 : ℝ) ≤ T := T.2
  have hu : Set.uIcc (0 : ℝ) T = Set.Icc (0 : ℝ) T := Set.uIcc_of_le hT0
  have iM : IntervalIntegrable fM volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).mpr hiM
  have iJ : IntervalIntegrable fJ volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).mpr hiJ
  set m : ℝ → ℝ := fun x => (c.G - ∫ r in (0 : ℝ)..T, fM r) + ∫ r in (0 : ℝ)..x, fM r with hm
  set j : ℝ → ℝ := fun x => (c.G / c.h - ∫ r in (0 : ℝ)..T, fJ r) + ∫ r in (0 : ℝ)..x, fJ r
    with hj
  have hIcc : ∀ (f : ℝ → ℝ), IntervalIntegrable f volume 0 T → ∀ x ∈ Set.Icc (0 : ℝ) T,
      ∫ r in Set.Icc x (T : ℝ), f r = (∫ r in (0 : ℝ)..T, f r) - ∫ r in (0 : ℝ)..x, f r := by
    intro f hf x hx
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.2,
      intervalIntegral.integral_interval_sub_left hf
        (hf.mono_set (by rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hT0]
                         exact Set.Icc_subset_Icc le_rfl hx.2))]
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) T, x.toNNReal ≤ T := fun x hx => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx.1]; exact hx.2
  have hmeq : ∀ x ∈ Set.Icc (0 : ℝ) T, M x.toNNReal = m x := by
    intro x hx
    have h1 := (heq x.toNNReal (hle x hx)).1
    rw [Real.coe_toNNReal _ hx.1, hIcc fM iM x hx] at h1
    rw [h1]; simp only [hm]; ring
  have hjeq : ∀ x ∈ Set.Icc (0 : ℝ) T, J x.toNNReal = j x := by
    intro x hx
    have h1 := (heq x.toNNReal (hle x hx)).2
    rw [Real.coe_toNNReal _ hx.1, hIcc fJ iJ x hx] at h1
    rw [h1]; simp only [hj]; ring
  have hposR : ∀ x ∈ Set.Icc (0 : ℝ) T, 0 < M x.toNNReal ∧ 0 < J x.toNNReal := fun x hx =>
    hpos _ (hle x hx)
  have hmAC : AbsolutelyContinuousOnInterval m 0 T :=
    ac_const_add _ (iM.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc)
  have hjAC : AbsolutelyContinuousOnInterval j 0 T :=
    ac_const_add _ (iJ.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc)
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hT0)
    (hu ▸ hjAC.continuousOn)
  have hκ : 0 < j x0 := by rw [← hjeq x0 hx0]; exact (hposR x0 hx0).2
  have hjinvAC : AbsolutelyContinuousOnInterval (fun x => (j x)⁻¹) 0 T :=
    ac_inv hjAC hκ (fun x hx => hmin (hu ▸ hx))
  set n : ℝ → ℝ := fun x => m x * (j x)⁻¹ with hn
  have hnAC : AbsolutelyContinuousOnInterval n 0 T := hmAC.fun_mul hjinvAC
  set g : ℝ → ℝ := fun r => rhs49N c T r.toNNReal (M r.toNNReal) (M r.toNNReal / J r.toNNReal)
    with hg
  have hderiv : ∀ᵐ x, x ∈ Set.Icc (0 : ℝ) T → deriv n x = g x := by
    filter_upwards [iM.ae_hasDerivAt_integral, iJ.ae_hasDerivAt_integral] with x h1 h2 hx
    have hx' : x ∈ Set.uIcc (0 : ℝ) T := hu ▸ hx
    have dm : HasDerivAt m (fM x) x := (h1 hx' 0 Set.left_mem_uIcc).const_add _
    have dj : HasDerivAt j (fJ x) x := (h2 hx' 0 Set.left_mem_uIcc).const_add _
    have hjx : j x ≠ 0 := by rw [← hjeq x hx]; exact (hposR x hx).2.ne'
    have dn : HasDerivAt n (fM x * (j x)⁻¹ + m x * (-(fJ x) / j x ^ 2)) x := dm.mul (dj.inv hjx)
    rw [dn.deriv, ← hmeq x hx, ← hjeq x hx]
    exact alg c T x.toNNReal _ _ (hposR x hx).1.ne' (hposR x hx).2.ne'
  have hTmem : (T : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨hT0, le_rfl⟩
  have hmT : m T = c.G := by simp only [hm]; ring
  have hjT : j T = c.G / c.h := by simp only [hj]; ring
  have hG : 0 < c.G := by rw [← hmT, ← hmeq _ hTmem]; exact (hposR _ hTmem).1
  have hGh : 0 < c.G / c.h := by rw [← hjT, ← hjeq _ hTmem]; exact (hposR _ hTmem).2
  have hh : c.h ≠ 0 := by
    intro h0; rw [h0, div_zero] at hGh; exact lt_irrefl _ hGh
  have hnT : n T = c.h := by
    simp only [hn, hmT, hjT]; field_simp
  refine ⟨⟨hU, ?_, ?_, fun s hs => ⟨?_, ?_⟩⟩, fun s hs => ⟨(hpos s hs).1,
    div_pos (hpos s hs).1 (hpos s hs).2⟩⟩
  · simp only [rhs49M_eq]; exact hiM
  · have := (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).mp hnAC.intervalIntegrable_deriv
    exact this.congr_fun_ae ((ae_restrict_iff' measurableSet_Icc).mpr hderiv)
  · simp only [rhs49M_eq]; exact (heq s hs).1
  · have hs' : (s : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨s.2, hs⟩
    show M s / J s = c.h - ∫ r in Set.Icc (s : ℝ) T, g r
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs'.2]
    have hcongr : ∫ r in (s : ℝ)..T, g r = ∫ r in (s : ℝ)..T, deriv n r := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with x hx hxI
      rw [Set.uIoc_of_le hs'.2] at hxI
      exact (hx ⟨s.2.trans hxI.1.le, hxI.2⟩).symm
    rw [hcongr, (hnAC.mono (by
      rw [Set.uIcc_of_le hs'.2, hu]; exact Set.Icc_subset_Icc s.2 le_rfl)).integral_deriv_eq_sub,
      hnT]
    have h1 := hmeq _ hs'
    have h2 := hjeq _ hs'
    rw [Real.toNNReal_coe] at h1 h2
    simp only [hn, ← h1, ← h2, div_eq_mul_inv]
    ring
