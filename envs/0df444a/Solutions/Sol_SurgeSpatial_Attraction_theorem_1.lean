-- Prove2me | solution 1 for SurgeSpatial.Attraction.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T20:25:27.955207+00:00
-- url     : https://prove2.me/submissions/fb544ca4-133e-444b-9b9f-b0e7860fa6bc

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting

set_option autoImplicit false

open MeasureTheory

namespace C2109

open SurgeSpatial.Attraction
open scoped ENNReal

noncomputable def e : E := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

theorem norm_e : ‖e‖ = 1 := by simp [e]

noncomputable def t (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem t_pos (n : ℕ) : 0 < t n := by
  unfold t; positivity

theorem t_le_one (n : ℕ) : t n ≤ 1 := by
  unfold t
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

noncomputable def pts (n : ℕ) : E := t n • e

theorem norm_pts (n : ℕ) : ‖pts n‖ = t n := by
  unfold pts
  rw [norm_smul, norm_e, mul_one, Real.norm_eq_abs, abs_of_pos (t_pos n)]

noncomputable def Γ0 : Measure E :=
  Measure.dirac 0 + Measure.sum (fun n : ℕ => ((2⁻¹ : ℝ≥0∞) ^ n) • Measure.dirac (pts n))

noncomputable def Fcdf (_y : E) (q : ℝ) : ℝ := max 0 (min 1 q)

noncomputable def M0 : Market where
  C := Metric.closedBall e 1
  Γ := Γ0
  Λ := Γ0
  Θ := 0
  F := Fcdf
  Vbar := 1
  α := 1 / 2

noncomputable def p0 (y : E) : ℝ := max 0 (1 - ‖y‖)

theorem M0_α : M0.α = 1 / 2 := rfl

theorem Fbar_eq (y : E) (q : ℝ) : M0.Fbar y q = 1 - Fcdf y q := rfl

theorem zero_mem_C : (0 : E) ∈ M0.C := by
  show (0 : E) ∈ Metric.closedBall e 1
  rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_e]

theorem pts_mem (n : ℕ) : pts n ∈ M0.C := by
  show pts n ∈ Metric.closedBall e 1
  have h : pts n - e = (t n - 1) • e := by unfold pts; rw [sub_smul, one_smul]
  rw [Metric.mem_closedBall, dist_eq_norm, h, norm_smul, norm_e, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [t_le_one n])]
  linarith [t_pos n]

theorem norm_le_two {y : E} (hy : y ∈ M0.C) : ‖y‖ ≤ 2 := by
  have h : y ∈ Metric.closedBall e 1 := hy
  have := norm_le_of_mem_closedBall h
  rw [norm_e] at this
  linarith

theorem C_meas : MeasurableSet M0.C := Metric.isClosed_closedBall.measurableSet

theorem finΓ0 : IsFiniteMeasure Γ0 := by
  constructor
  unfold Γ0
  rw [Measure.add_apply, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.ofNat_lt_top⟩

theorem Γ0_compl : Γ0 M0.Cᶜ = 0 := by
  have hm : MeasurableSet M0.Cᶜ := C_meas.compl
  unfold Γ0
  rw [Measure.add_apply, Measure.sum_apply _ hm]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hm, smul_eq_mul]
  simp [Set.indicator, zero_mem_C, pts_mem]

theorem atom0 : Γ0 {0} ≠ 0 := by
  unfold Γ0
  rw [Measure.add_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _)]
  simp

theorem atom_pts (n : ℕ) : (M0.Γ.restrict M0.C) {pts n} ≠ 0 := by
  intro h
  rw [Measure.restrict_apply (measurableSet_singleton _),
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (pts_mem n))] at h
  have hle : ((2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac (pts n)) {pts n} ≤ Γ0 {pts n} := by
    calc ((2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac (pts n)) {pts n}
        ≤ Measure.sum (fun k : ℕ => ((2⁻¹ : ℝ≥0∞) ^ k) • Measure.dirac (pts k)) {pts n} :=
          Measure.le_iff'.1 (Measure.le_sum _ n) _
      _ ≤ Γ0 {pts n} := by unfold Γ0; rw [Measure.add_apply]; exact le_add_self
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul,
    mul_one] at hle
  have h0 : (2⁻¹ : ℝ≥0∞) ^ n = 0 := le_antisymm (hle.trans (le_of_eq h)) bot_le
  exact pow_ne_zero n (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) h0

theorem atom0_restrict : (M0.Γ.restrict M0.C) {0} ≠ 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton _),
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 zero_mem_C)]
  exact atom0

theorem atom_of_ae {μ : Measure E} {P : E → Prop} (h : ∀ᵐ y ∂μ, P y) (x : E)
    (hx : μ {x} ≠ 0) : P x := by
  by_contra hP
  exact hx (measure_mono_null (Set.singleton_subset_iff.2 hP) (ae_iff.1 h))

theorem hlam : ∀ᵐ y ∂M0.Γ, 0 < M0.lam y := by
  haveI := finΓ0
  show ∀ᵐ y ∂Γ0, 0 < (Γ0.rnDeriv Γ0 y).toReal
  filter_upwards [Measure.rnDeriv_self Γ0] with y hy
  rw [hy]
  norm_num

theorem hsT0 : ∀ᵐ y ∂M0.Γ, M0.sT 0 y = 0 := by
  show ∀ᵐ y ∂Γ0, ((Measure.map Prod.snd (0 : Measure (E × E))).rnDeriv Γ0 y).toReal = 0
  rw [Measure.map_zero]
  filter_upwards [Measure.rnDeriv_zero Γ0] with y hy
  rw [hy]
  rfl

theorem R_le_one (y : E) (q s : ℝ) : M0.R y q s ≤ 1 := by
  unfold Market.R
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl
  · norm_num

theorem Fcdf_le_one (y : E) (q : ℝ) : Fcdf y q ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem R_nonneg (y : E) (q s : ℝ) (hs : 0 ≤ s) : 0 ≤ M0.R y q s := by
  have hF : 0 ≤ M0.Fbar y q := by rw [Fbar_eq]; linarith [Fcdf_le_one y q]
  have hl : 0 ≤ M0.lam y := ENNReal.toReal_nonneg
  unfold Market.R
  split_ifs with h1 h2
  · exact le_min zero_le_one (div_nonneg (mul_nonneg hl hF) h1.le)
  · exact zero_le_one
  · exact le_rfl

theorem R_at_one (y : E) (s : ℝ) : M0.R y 1 s = 0 := by
  have h : M0.Fbar y 1 = 0 := by rw [Fbar_eq]; simp [Fcdf]
  unfold Market.R
  simp [h]

theorem Ufun_lt (y : E) (q s : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : M0.Ufun y q s < 1 / 2 := by
  unfold Market.Ufun
  rw [M0_α]
  rcases eq_or_lt_of_le hq.2 with h | h
  · subst h
    rw [R_at_one]
    norm_num
  · have h1 : q * M0.R y q s ≤ q * 1 := mul_le_mul_of_nonneg_left (R_le_one y q s) hq.1
    have h2 : 1 / 2 * q * M0.R y q s = 1 / 2 * (q * M0.R y q s) := by ring
    rw [h2]
    linarith

theorem p0_mem (y : E) : p0 y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by linarith [norm_nonneg y])⟩

theorem Pi_le (T : Measure (E × E)) (x y : E) : M0.Pi p0 T x y ≤ 1 / 2 := by
  unfold Market.Pi Market.U
  have := Ufun_lt y (p0 y) (M0.sT T y) (p0_mem y)
  linarith [norm_nonneg (y - x)]

theorem Pi_ge (T : Measure (E × E)) (x y : E) (hy : y ∈ M0.C) :
    -2 - ‖x‖ ≤ M0.Pi p0 T x y := by
  unfold Market.Pi Market.U Market.Ufun
  rw [M0_α]
  have hR := R_nonneg y (p0 y) (M0.sT T y) ENNReal.toReal_nonneg
  have hp := (p0_mem y).1
  have hU : 0 ≤ 1 / 2 * p0 y * M0.R y (p0 y) (M0.sT T y) := by positivity
  have h1 := norm_sub_le y x
  have h2 := norm_le_two hy
  linarith

theorem Pi_pts (n : ℕ) (hl : 0 < M0.lam (pts n)) (hs : M0.sT 0 (pts n) = 0) :
    M0.Pi p0 0 0 (pts n) = (1 - t n) / 2 - t n := by
  have hp : p0 (pts n) = 1 - t n := by
    unfold p0; rw [norm_pts]; exact max_eq_right (by linarith [t_le_one n])
  have hF : M0.Fbar (pts n) (1 - t n) = t n := by
    rw [Fbar_eq]; unfold Fcdf
    rw [min_eq_right (by linarith [t_pos n]), max_eq_right (by linarith [t_le_one n])]
    ring
  have hR : M0.R (pts n) (1 - t n) 0 = 1 := by
    unfold Market.R
    rw [hF]
    simp [mul_pos hl (t_pos n)]
  unfold Market.Pi Market.U Market.Ufun
  rw [hs, hp, hR, M0_α, sub_zero, norm_pts]
  ring

theorem V0_ge : (1 / 2 : ℝ) ≤ M0.V p0 0 0 := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hc : M0.V p0 0 0 < (M0.V p0 0 0 + 1 / 2) / 2 := by linarith
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) (ae (M0.Γ.restrict M0.C))
      (fun y => M0.Pi p0 0 0 y) := Filter.isBoundedUnder_of ⟨1 / 2, fun y => Pi_le 0 0 y⟩
  have h1 : ∀ᵐ y ∂(M0.Γ.restrict M0.C), M0.Pi p0 0 0 y < (M0.V p0 0 0 + 1 / 2) / 2 :=
    ae_lt_of_essSup_lt hc hbdd
  have h2 : ∀ᵐ y ∂(M0.Γ.restrict M0.C), 0 < M0.lam y := ae_restrict_of_ae hlam
  have h3 : ∀ᵐ y ∂(M0.Γ.restrict M0.C), M0.sT 0 y = 0 := ae_restrict_of_ae hsT0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ)
    (show (0 : ℝ) < (1 / 2 - (M0.V p0 0 0 + 1 / 2) / 2) / 2 by linarith)
  obtain ⟨hlt', hl', hs'⟩ := atom_of_ae (h1.and (h2.and h3)) (pts n) (atom_pts n)
  rw [Pi_pts n hl' hs'] at hlt'
  have htn : t n = 1 / ((n : ℝ) + 1) := rfl
  linarith

theorem V_le (x : E) : M0.V p0 0 x ≤ 1 / 2 := by
  have hne : M0.Γ.restrict M0.C ≠ 0 := fun h => atom0_restrict (by rw [h]; rfl)
  haveI : (ae (M0.Γ.restrict M0.C)).NeBot := ae_neBot.2 hne
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae (M0.Γ.restrict M0.C))
      (fun y => M0.Pi p0 0 x y) := by
    apply Filter.isCoboundedUnder_le_of_eventually_le _ (x := -2 - ‖x‖)
    filter_upwards [ae_restrict_mem C_meas] with y hy
    exact Pi_ge 0 x y hy
  exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall (fun y => Pi_le 0 x y)) hcob

theorem zero_mem_attr : (0 : E) ∈ M0.attr p0 0 0 :=
  ⟨zero_mem_C, zero_mem_C, by simp⟩

theorem sink : M0.IsSink p0 0 0 := by
  refine ⟨⟨0, zero_mem_attr⟩, fun z' _ hne hmem => ?_⟩
  have h := hmem.2.2
  rw [sub_zero] at h
  have hpos : 0 < ‖z'‖ := norm_pos_iff.2 hne
  linarith [V_le z', V0_ge]

theorem standing : M0.Standing := by
  haveI := finΓ0
  refine
    { convex_C := convex_closedBall e 1
      compact_C := isCompact_closedBall e 1
      finite_Γ := finΓ0
      finite_Λ := finΓ0
      finite_Θ := by show IsFiniteMeasure (0 : Measure E); infer_instance
      Γ_conc := Γ0_compl
      Λ_conc := Γ0_compl
      Θ_conc := rfl
      Λ_ac := Measure.AbsolutelyContinuous.rfl
      Θ_ac := Measure.AbsolutelyContinuous.zero _
      Vbar_pos := by show (0 : ℝ) < 1; norm_num
      α_pos := by show (0 : ℝ) < 1 / 2; norm_num
      α_lt_one := by show (1 / 2 : ℝ) < 1; norm_num
      F_mono := fun y _ a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
      F_nonneg := fun y _ q => le_max_left _ _
      F_le_one := fun y _ q => Fcdf_le_one y q
      F_neg := fun y _ q hq => max_eq_left ((min_le_right _ _).trans hq.le)
      F_Vbar := fun y _ => by show max 0 (min 1 (1 : ℝ)) = 1; norm_num
      F_strictMono := ?_
      revenue_cont := ?_
      revenue_unimodal := ?_
      lam_pos := hlam
      F_meas := ?_ }
  · intro y _ a ha b hb hab
    have ha2 : a ≤ 1 := ha.2
    have hb2 : b ≤ 1 := hb.2
    show max 0 (min 1 a) < max 0 (min 1 b)
    rw [min_eq_right ha2, min_eq_right hb2, max_eq_right ha.1, max_eq_right hb.1]
    exact hab
  · intro y _
    exact (show Continuous (fun q : ℝ => q * (1 - max 0 (min 1 q))) by fun_prop).continuousOn
  · intro y _
    have hrev : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q * M0.Fbar y q = q * (1 - q) := by
      intro q h0 h1
      rw [Fbar_eq]; unfold Fcdf; rw [min_eq_right h1, max_eq_right h0]
    refine ⟨1 / 2, ⟨by norm_num, by show (1 / 2 : ℝ) ≤ 1; norm_num⟩, ?_, ?_⟩
    · intro a ha b hb hab
      have ha2 : a ≤ 1 / 2 := ha.2
      have hb2 : b ≤ 1 / 2 := hb.2
      show a * M0.Fbar y a < b * M0.Fbar y b
      rw [hrev a ha.1 (by linarith), hrev b hb.1 (by linarith)]
      nlinarith [mul_pos (sub_pos.2 hab) (show (0 : ℝ) < 1 - a - b by linarith)]
    · intro a ha b hb hab
      have ha2 : a ≤ 1 := ha.2
      have hb2 : b ≤ 1 := hb.2
      show b * M0.Fbar y b < a * M0.Fbar y a
      rw [hrev a (by linarith [ha.1]) ha2, hrev b (by linarith [hb.1]) hb2]
      nlinarith [mul_pos (sub_pos.2 hab) (show (0 : ℝ) < a + b - 1 by linarith [ha.1])]
  · exact (show Continuous (fun x : E × ℝ => max 0 (min 1 x.2)) by fun_prop).measurable

theorem feasible : M0.FeasibleP2 p0 0 := by
  refine ⟨?_, fun y _ => p0_mem y, ⟨inferInstance, by simp, ?_, ?_⟩, ?_⟩
  · exact (show Continuous p0 by unfold p0; fun_prop).measurable
  · rw [Measure.map_zero]; rfl
  · rw [Measure.map_zero]; exact Measure.AbsolutelyContinuous.zero _
  · show (0 : Measure (E × E)) _ = (0 : Measure E) _
    simp

theorem a0_mem : -e ∈ Metric.sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_neg, norm_e]

noncomputable def a0 : S1 := ⟨-e, a0_mem⟩

theorem Xend_a0 : M0.Xend p0 0 0 a0 = 0 := by
  unfold Market.Xend
  have hS : {t : ℝ | 0 ≤ t ∧ (0 : E) + t • (a0 : E) ∈ M0.attr p0 0 0} ⊆ {0} := by
    intro s hs
    obtain ⟨hs0, hmem⟩ := hs
    have hC : dist ((0 : E) + s • (-e)) e ≤ 1 := hmem.1
    have h : (0 : E) + s • (-e) - e = (-(s + 1)) • e := by module
    rw [dist_eq_norm, h, norm_smul, norm_e, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by linarith)] at hC
    show s = 0
    linarith
  rcases Set.subset_singleton_iff_eq.1 hS with h | h
  · rw [h, Real.sSup_empty, zero_smul, add_zero]
  · rw [h, csSup_singleton, zero_smul, add_zero]

end C2109

open SurgeSpatial.Attraction in
theorem solution : ¬ (∀ (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z),
    ∃ (pHat : E → ℝ) (THat : Measure (E × E)) (r : S1 → E) (s : S1 → ℝ),
      M.FeasibleP2 pHat THat ∧ M.objP2 p T ≤ M.objP2 pHat THat ∧
      (∀ a, r a ∈ segment ℝ z (M.Xend p T z a) ∧ 0 ≤ s a) ∧
      ∀ᵐ x ∂M.Γ, x ∈ M.attr p T z →
        (x ∈ ⋃ a, (segment ℝ z (r a) \ {r a}) →
            M.psi x (M.sT THat x) = M.V p T z - ‖x - z‖) ∧
        (∀ a, x = r a → x ∉ ⋃ b, (segment ℝ z (r b) \ {r b}) → M.sT THat x = s a) ∧
        (x ∉ ⋃ a, segment ℝ z (r a) → M.sT THat x = 0) ∧
        ((∀ a, x ≠ r a) → pHat x = M.rhoLoc x (M.sT THat x)) ∧
        (∀ a, x = r a → M.Ufun x (pHat x) (s a) = M.V p T x)) := by
  intro H
  obtain ⟨pHat, THat, r, s, hfeas, -, hr, hae⟩ :=
    H C2109.M0 C2109.standing C2109.p0 0 C2109.feasible 0 C2109.zero_mem_C C2109.sink
  have hr0 : r C2109.a0 = 0 := by
    have h := (hr C2109.a0).1
    rw [C2109.Xend_a0, segment_same] at h
    exact h
  have hx := C2109.atom_of_ae hae 0 C2109.atom0
  beta_reduce at hx
  have h5 := (hx C2109.zero_mem_attr).2.2.2.2 C2109.a0 hr0.symm
  have hq : pHat 0 ∈ Set.Icc (0 : ℝ) 1 := hfeas.2.1 0 C2109.zero_mem_C
  have h6 := C2109.Ufun_lt 0 (pHat 0) (s C2109.a0) hq
  have h7 := C2109.V0_ge
  linarith
