-- Prove2me | solution 1 for SelfishMiningRuin.ValueFn.equation_29
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:56:03.659192+00:00
-- url     : https://prove2.me/submissions/cf5bdd6e-e3b7-4a49-a20c-46a6a277a516
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model
import Theorems.Thm_SelfishMiningRuin_ValueFn_Vhat_conditioning
import Theorems.Thm_SelfishMiningRuin_ValueFn_Vhat_linear_bound

set_option autoImplicit false

namespace SMRSol29

open Set Filter Topology

/-- Analytic core: the conditioning identity plus linear growth give differentiability and the
first-order equation `c V' + β V = u/t + λ H`. -/
lemma deriv_of_cond {ι : Type*} (V Hm : ι → ℝ → ℝ) (lam c t b K : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (ht : 0 < t) (hb : 0 < b) (hK0 : 0 ≤ K)
    (hK : ∀ z u, 0 ≤ u → |V z u| ≤ K * u)
    (hHbd : ∀ z v, 0 ≤ v → |Hm z v| ≤ K * (v + 2 * b))
    (hHcont : (∀ z, ContinuousOn (V z) (Ici 0)) → ∀ z, ContinuousOn (Hm z) (Ici 0))
    (hcond : ∀ z u h, 0 ≤ h → c * h ≤ u →
      V z u = Real.exp (-(lam + 1 / t) * h) * V z (u - c * h) +
        ∫ s in (0 : ℝ)..h, Real.exp (-(lam + 1 / t) * s) *
          ((u - c * s) / t + lam * Hm z (u - c * s))) :
    (∀ z, V z 0 = 0) ∧
    ∀ z u, 0 < u → HasDerivAt (V z) ((u / t + lam * Hm z u - (lam + 1 / t) * V z u) / c) u := by
  set β := lam + 1 / t with hβ
  have hβ0 : 0 < β := by positivity
  have hV0 : ∀ z, V z 0 = 0 := by
    intro z
    have := hK z 0 le_rfl
    rw [mul_zero] at this
    exact abs_nonpos_iff.mp this
  refine ⟨hV0, ?_⟩
  -- bound on the integrand
  set M : ℝ → ℝ := fun y => y / t + lam * (K * (y + 2 * b)) with hM
  have hGbd : ∀ z u s, 0 ≤ s → c * s ≤ u →
      ‖Real.exp (-β * s) * ((u - c * s) / t + lam * Hm z (u - c * s))‖ ≤ M u := by
    intro z u s hs hcs
    have hv : 0 ≤ u - c * s := by linarith
    have he : Real.exp (-β * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 ≤ Real.exp (-β * s) := (Real.exp_pos _).le
    have hH := hHbd z (u - c * s) hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he0]
    have h1 : |(u - c * s) / t + lam * Hm z (u - c * s)| ≤ M u := by
      calc _ ≤ |(u - c * s) / t| + |lam * Hm z (u - c * s)| := abs_add_le _ _
        _ = (u - c * s) / t + lam * |Hm z (u - c * s)| := by
            rw [abs_of_nonneg (by positivity), abs_mul, abs_of_pos hlam]
        _ ≤ u / t + lam * (K * (u + 2 * b)) := by
            have : (u - c * s) / t ≤ u / t := by
              apply div_le_div_of_nonneg_right _ ht.le
              nlinarith
            have : K * (u - c * s + 2 * b) ≤ K * (u + 2 * b) := by
              apply mul_le_mul_of_nonneg_left _ hK0; nlinarith
            nlinarith
    have hM0 : 0 ≤ M u := le_trans (abs_nonneg _) h1
    calc Real.exp (-β * s) * |(u - c * s) / t + lam * Hm z (u - c * s)|
        ≤ 1 * M u := mul_le_mul he h1 (abs_nonneg _) zero_le_one
      _ = M u := one_mul _
  have hMmono : ∀ x y, x ≤ y → M x ≤ M y := by
    intro x y hxy
    simp only [hM]
    have : x / t ≤ y / t := div_le_div_of_nonneg_right hxy ht.le
    have : K * (x + 2 * b) ≤ K * (y + 2 * b) := mul_le_mul_of_nonneg_left (by linarith) hK0
    nlinarith
  -- local Lipschitz estimate
  have hLip : ∀ z x y, 0 ≤ x → x ≤ y →
      |V z y - V z x| ≤ (M y + β * (K * y)) / c * (y - x) := by
    intro z x y hx hxy
    set h := (y - x) / c with hh
    have hh0 : 0 ≤ h := div_nonneg (by linarith) hc.le
    have hch : c * h = y - x := by rw [hh]; field_simp
    have hid := hcond z y h hh0 (by rw [hch]; linarith)
    have hyx : y - c * h = x := by rw [hch]; ring
    rw [hyx] at hid
    have hI : ‖∫ s in (0 : ℝ)..h, Real.exp (-β * s) * ((y - c * s) / t + lam * Hm z (y - c * s))‖
        ≤ M y * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hh0] at hs
      apply hGbd z y s hs.1.le
      nlinarith [hs.2]
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh0] at hI
    have hexp : 0 ≤ 1 - Real.exp (-β * h) ∧ 1 - Real.exp (-β * h) ≤ β * h := by
      constructor
      · have : Real.exp (-β * h) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      · have := Real.add_one_le_exp (-β * h)
        linarith
    have hVx := hK z x hx
    have hKxy : K * x ≤ K * y := mul_le_mul_of_nonneg_left hxy hK0
    have hβ' : -(lam + 1 / t) = -β := by rw [hβ]
    rw [hβ'] at hid
    rw [hid]
    generalize (∫ s in (0 : ℝ)..h, Real.exp (-β * s) *
      ((y - c * s) / t + lam * Hm z (y - c * s))) = I at hI ⊢
    calc |Real.exp (-β * h) * V z x + I - V z x|
        = |I - (1 - Real.exp (-β * h)) * V z x| := by congr 1; ring
      _ ≤ |I| + |(1 - Real.exp (-β * h)) * V z x| := abs_sub _ _
      _ ≤ M y * h + (β * h) * (K * y) := by
          gcongr
          rw [abs_mul, abs_of_nonneg hexp.1]
          calc (1 - Real.exp (-β * h)) * |V z x| ≤ (β * h) * (K * x) :=
                mul_le_mul hexp.2 hVx (abs_nonneg _) (by positivity)
            _ ≤ (β * h) * (K * y) := mul_le_mul_of_nonneg_left hKxy (by positivity)
      _ = (M y + β * (K * y)) / c * (y - x) := by
          rw [hh]; field_simp
  -- continuity on [0, ∞)
  have hcont : ∀ z, ContinuousOn (V z) (Ici 0) := by
    intro z u hu
    have hu0 : (0 : ℝ) ≤ u := hu
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    set L := (M (u + 1) + β * (K * (u + 1))) / c with hL
    have hL0 : 0 ≤ L := by
      have : 0 ≤ M (u + 1) := by simp only [hM]; positivity
      positivity
    refine ⟨min 1 (ε / (L + 1)), by positivity, fun {x} hx hdist => ?_⟩
    have hx0 : (0 : ℝ) ≤ x := hx
    rw [Real.dist_eq] at hdist ⊢
    have hd1 : |x - u| < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 : |x - u| < ε / (L + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
    have key : |V z x - V z u| ≤ L * |x - u| := by
      rcases le_total x u with hxu | hux
      · have := hLip z x u hx0 hxu
        rw [abs_sub_comm, abs_sub_comm x u, abs_of_nonneg (by linarith : 0 ≤ u - x)]
        refine this.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
        apply div_le_div_of_nonneg_right _ hc.le
        have := hMmono u (u + 1) (by linarith)
        have : K * u ≤ K * (u + 1) := mul_le_mul_of_nonneg_left (by linarith) hK0
        nlinarith
      · have := hLip z u x hu0 hux
        rw [abs_of_nonneg (by linarith : 0 ≤ x - u)]
        refine this.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
        apply div_le_div_of_nonneg_right _ hc.le
        have hx1 : x ≤ u + 1 := by
          have := (abs_lt.mp hd1).2
          linarith
        have := hMmono x (u + 1) hx1
        have : K * x ≤ K * (u + 1) := mul_le_mul_of_nonneg_left hx1 hK0
        nlinarith
    calc |V z x - V z u| ≤ L * |x - u| := key
      _ ≤ (L + 1) * |x - u| := by nlinarith [abs_nonneg (x - u)]
      _ < (L + 1) * (ε / (L + 1)) := by
          apply mul_lt_mul_of_pos_left hd2; positivity
      _ = ε := by field_simp
  have hHc := hHcont hcont
  -- the integrand G
  set G : ι → ℝ → ℝ := fun z v => v / t + lam * Hm z v with hG
  have hGc : ∀ z, ContinuousOn (G z) (Ici 0) := by
    intro z
    exact (continuousOn_id.div_const t).add (continuousOn_const.mul (hHc z))
  -- integral representation
  have hrep : ∀ z u, 0 ≤ u → V z u = c⁻¹ * (Real.exp (-(β / c) * u) *
      ∫ v in (0 : ℝ)..u, Real.exp ((β / c) * v) * G z v) := by
    intro z u hu
    have hid := hcond z u (u / c) (by positivity) (by rw [mul_div_cancel₀ _ hc.ne'])
    rw [mul_div_cancel₀ _ hc.ne', sub_self, hV0, mul_zero, zero_add] at hid
    rw [hid]
    have hcongr : (∫ s in (0 : ℝ)..(u / c), Real.exp (-(lam + 1 / t) * s) *
        ((u - c * s) / t + lam * Hm z (u - c * s))) =
        ∫ s in (0 : ℝ)..(u / c), (fun v => Real.exp (-(β / c) * u) *
          (Real.exp ((β / c) * v) * G z v)) (u - c * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hG, hβ]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_comp_sub_mul (fun v => Real.exp (-(β / c) * u) *
          (Real.exp ((β / c) * v) * G z v)) hc.ne', mul_div_cancel₀ _ hc.ne',
      sub_self, mul_zero, sub_zero, intervalIntegral.integral_const_mul, smul_eq_mul]
  intro z u hu
  -- derivative of the integral
  have hfc : ContinuousOn (fun v => Real.exp ((β / c) * v) * G z v) (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (hGc z)
  have hΦ : HasDerivAt (fun x => ∫ v in (0 : ℝ)..x, Real.exp ((β / c) * v) * G z v)
      (Real.exp ((β / c) * u) * G z u) u := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hfc.mono (by
        rw [uIcc_of_le hu.le]; exact Icc_subset_Ici_self)).intervalIntegrable
    · exact (hfc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi u hu
    · exact hfc.continuousAt (Ici_mem_nhds hu)
  have hE : HasDerivAt (fun x => Real.exp (-(β / c) * x)) (Real.exp (-(β / c) * u) * (-(β / c))) u := by
    have := ((hasDerivAt_id' u).const_mul (-(β / c))).exp
    simpa using this
  have hD := (hE.mul hΦ).const_mul c⁻¹
  have hev : (fun x => c⁻¹ * (Real.exp (-(β / c) * x) *
      ∫ v in (0 : ℝ)..x, Real.exp ((β / c) * v) * G z v)) =ᶠ[𝓝 u] V z := by
    filter_upwards [Ici_mem_nhds hu] with x hx
    exact (hrep z x hx).symm
  have hD' := hD.congr_of_eventuallyEq hev.symm
  refine hD'.congr_deriv ?_
  rw [hrep z u hu.le]
  generalize (∫ v in (0 : ℝ)..u, Real.exp ((β / c) * v) * G z v) = Φ
  have hEE : Real.exp (-(β / c) * u) * Real.exp ((β / c) * u) = 1 := by
    rw [← Real.exp_add]; simp
  rw [← mul_assoc (Real.exp (-(β / c) * u)) (Real.exp ((β / c) * u)), hEE, one_mul]
  simp only [hG]
  field_simp
  ring

end SMRSol29

open SelfishMiningRuin.ValueFn Set SMRSol29

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) :
    let F0 := fun u => Vhat P W ξ ζ c b u t St.zero
    let F1 := fun u => Vhat P W ξ ζ c b u t St.one
    let Ff := fun u => Vhat P W ξ ζ c b u t St.fork
    F0 0 = 0 ∧ F1 0 = 0 ∧ Ff 0 = 0 ∧
    ∀ u : ℝ, 0 < u →
      (HasDerivAt F0 (deriv F0 u) u ∧
       HasDerivAt F1 (deriv F1 u) u ∧
       HasDerivAt Ff (deriv Ff u) u) ∧
      0 = c*deriv F0 u + (lam*p + 1/t)*F0 u - lam*p*F1 u - u/t ∧
      0 = c*deriv F1 u + (lam + 1/t)*F1 u - lam*p*F0 (u+2*b) -
        lam*(1-p)*Ff u - u/t ∧
      0 = c*deriv Ff u + (lam + 1/t)*Ff u - lam*p*F0 (u+2*b) -
        lam*(1-p)*q*F0 (u+b) - lam*(1-p)*(1-q)*F0 u - u/t := by
  obtain ⟨Kv, hKv⟩ := Vhat_linear_bound P W ξ ζ lam c b t p q hlam hc hb ht hp0 hp1 hq0 hq1 hprim
  have hcondP := Vhat_conditioning P W ξ ζ lam c b t p q hlam hc hb ht hp0 hp1 hq0 hq1 hprim
  have hK : ∀ z u, 0 ≤ u → |Vhat P W ξ ζ c b u t z| ≤ |Kv| * u := fun z u hu =>
    (hKv z u hu).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hu)
  have hrw : ∀ z x y, (reward z x y : ℝ) ≤ 2 := by
    intro z x y; cases z <;> cases x <;> cases y <;> simp [reward]
  have hrw0 : ∀ z x y, (0 : ℝ) ≤ (reward z x y : ℝ) := fun _ _ _ => Nat.cast_nonneg _
  have hw1 : 0 ≤ p * q := by positivity
  have hw2 : 0 ≤ p * (1 - q) := mul_nonneg hp0.le (by linarith)
  have hw3 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) hq0
  have hw4 : 0 ≤ (1 - p) * (1 - q) := mul_nonneg (by linarith) (by linarith)
  have hterm : ∀ (w : ℝ) (z : St) (x y : Bool) (v : ℝ), 0 ≤ w → 0 ≤ v →
      |w * Vhat P W ξ ζ c b (v + b * reward z x y) t (step z x y)| ≤ w * (|Kv| * (v + 2 * b)) := by
    intro w z x y v hw hv
    rw [abs_mul, abs_of_nonneg hw]
    apply mul_le_mul_of_nonneg_left _ hw
    refine (hK _ _ (by have := hrw0 z x y; positivity)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := hrw z x y
    nlinarith
  obtain ⟨h0, hd⟩ := deriv_of_cond (fun z u => Vhat P W ξ ζ c b u t z)
    (fun z v => p * q * Vhat P W ξ ζ c b (v + b * reward z true true) t (step z true true) +
      p * (1 - q) * Vhat P W ξ ζ c b (v + b * reward z true false) t (step z true false) +
      (1 - p) * q * Vhat P W ξ ζ c b (v + b * reward z false true) t (step z false true) +
      (1 - p) * (1 - q) * Vhat P W ξ ζ c b (v + b * reward z false false) t (step z false false))
    lam c t b |Kv| hlam hc ht hb (abs_nonneg _) hK
    (by
      intro z v hv
      have e1 := hterm _ z true true v hw1 hv
      have e2 := hterm _ z true false v hw2 hv
      have e3 := hterm _ z false true v hw3 hv
      have e4 := hterm _ z false false v hw4 hv
      refine ((abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)) _)).trans ?_
      refine (add_le_add (add_le_add (add_le_add e1 e2) e3) e4).trans (le_of_eq ?_)
      ring)
    (by
      intro hcont z
      have hcomp : ∀ (z' : St) (d : ℝ), 0 ≤ d →
          ContinuousOn (fun v => Vhat P W ξ ζ c b (v + d) t z') (Ici 0) := by
        intro z' d hd
        exact (hcont z').comp (continuousOn_id.add continuousOn_const)
          (fun v hv => by
            simp only [mem_Ici] at hv ⊢
            show 0 ≤ v + d
            linarith)
      have g := fun x y => hcomp (step z x y) (b * reward z x y) (by have := hrw0 z x y; positivity)
      exact ((((g true true).const_smul (p * q)).add ((g true false).const_smul (p * (1 - q)))).add
        ((g false true).const_smul ((1 - p) * q))).add ((g false false).const_smul ((1 - p) * (1 - q))))
    (fun z u h hh hch => hcondP z u h hh hch)
  intro F0 F1 Ff
  refine ⟨h0 St.zero, h0 St.one, h0 St.fork, fun u hu => ?_⟩
  have d0 := hd St.zero u hu
  have d1 := hd St.one u hu
  have df := hd St.fork u hu
  have e0 : deriv F0 u = _ := d0.deriv
  have e1 : deriv F1 u = _ := d1.deriv
  have ef : deriv Ff u = _ := df.deriv
  refine ⟨⟨by rw [e0]; exact d0, by rw [e1]; exact d1, by rw [ef]; exact df⟩, ?_, ?_, ?_⟩
  · rw [e0]
    simp only [F0, F1, reward, step, Nat.cast_zero, mul_zero, add_zero]
    field_simp
    ring
  · rw [e1]
    simp only [F0, F1, Ff, reward, step, Nat.cast_zero, Nat.cast_ofNat, mul_zero, add_zero]
    field_simp
    ring
  · rw [ef]
    simp only [F0, F1, Ff, reward, step, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero,
      add_zero, mul_one]
    field_simp
    ring
