-- Prove2me | solution 1 for StatComplexityDM.Estimation.hellinger_estimation_le_logloss_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:55:50.22666+00:00
-- url     : https://prove2.me/submissions/f3440470-3547-46d4-b6d5-5255aab01267

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_Estimation_Sequential
import Definitions.Def_StatComplexityDM_Estimation_Process

set_option autoImplicit false

open StatComplexityDM.Estimation in
theorem hel35_prod_le_one {Z : Type*} [Fintype Z] (T : ℕ)
    (K : (t : Fin T) → Hist Z t.val → Z → ℝ)
    (hK0 : ∀ t p z, 0 ≤ K t p z) (hK1 : ∀ t p, ∑ z, K t p z ≤ 1) :
    ∑ h : Hist Z T, ∏ t, K t (histPrefix h t) (h t) ≤ 1 := by
  induction T with
  | zero => simp
  | succ n ih =>
    have e : ∀ h : Hist Z (n+1), ∏ t, K t (histPrefix h t) (h t) =
        (∏ t : Fin n, K t.castSucc (histPrefix (Fin.init h) t) (Fin.init h t)) *
          K (Fin.last n) (Fin.init h) (h (Fin.last n)) := by
      intro h
      rw [Fin.prod_univ_castSucc]
      rfl
    simp_rw [e]
    rw [← (Fin.snocEquiv fun _ : Fin (n+1) => Z).sum_comp, Fintype.sum_prod_type_right]
    have ih' := ih (fun t => K t.castSucc) (fun t p z => hK0 t.castSucc p z) (fun t p => hK1 t.castSucc p)
    calc _ = ∑ h' : Hist Z n, (∏ t : Fin n, K t.castSucc (histPrefix h' t) (h' t)) *
          ∑ z, K (Fin.last n) h' z := by
            refine Finset.sum_congr rfl (fun h' _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            simp [Fin.snocEquiv]
      _ ≤ ∑ h' : Hist Z n, (∏ t : Fin n, K t.castSucc (histPrefix h' t) (h' t)) := by
            refine Finset.sum_le_sum (fun h' _ => ?_)
            have : 0 ≤ ∏ t : Fin n, K t.castSucc (histPrefix h' t) (h' t) :=
              Finset.prod_nonneg (fun t _ => hK0 _ _ _)
            calc _ ≤ (∏ t : Fin n, K t.castSucc (histPrefix h' t) (h' t)) * 1 :=
                  mul_le_mul_of_nonneg_left (hK1 _ _) this
              _ = _ := mul_one _
      _ ≤ 1 := ih'

open StatComplexityDM.Estimation FoundationsRL.GeneralDM in
theorem hel35_sqrt_sum {Y : Type*} [Fintype Y] (q r : Y → ℝ)
    (hq : StatComplexityDM.LowerBound.IsDist q) (hr : StatComplexityDM.LowerBound.IsDist r) :
    ∑ y, Real.sqrt (q y * r y) = 1 - hellingerSq q r / 2 := by
  have h1 : hellingerSq q r = ∑ y, (q y + r y - 2 * Real.sqrt (q y * r y)) := by
    unfold hellingerSq
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have e1 := Real.sq_sqrt (hq.1 y)
    have e2 := Real.sq_sqrt (hr.1 y)
    rw [Real.sqrt_mul (hq.1 y)]
    linear_combination e1 + e2
  rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, hq.2, hr.2, ← Finset.mul_sum]
  ring

open StatComplexityDM.Estimation FoundationsRL.GeneralDM StatComplexityDM.LowerBound in
theorem hel35_step {X Y : Type*} [Fintype X] [Fintype Y] (c : X → ℝ) (q r : X → Y → ℝ)
    (hc : IsDist c) (hq : ∀ x, IsDist (q x)) (hr : ∀ x, IsDist (r x)) :
    ∑ xy : X × Y, c xy.1 * Real.sqrt (q xy.1 xy.2 * r xy.1 xy.2) *
      Real.exp ((∑ x, c x * hellingerSq (q x) (r x)) / 2) ≤ 1 := by
  set E := ∑ x, c x * hellingerSq (q x) (r x) with hE
  rw [Fintype.sum_prod_type]
  have h3 : ∀ x, ∑ y, c x * Real.sqrt (q x y * r x y) * Real.exp (E / 2) =
      c x * (1 - hellingerSq (q x) (r x) / 2) * Real.exp (E / 2) := by
    intro x
    rw [← Finset.sum_mul, ← Finset.mul_sum, hel35_sqrt_sum _ _ (hq x) (hr x)]
  simp_rw [h3]
  rw [← Finset.sum_mul]
  have h4 : ∑ x, c x * (1 - hellingerSq (q x) (r x) / 2) = 1 - E / 2 := by
    calc ∑ x, c x * (1 - hellingerSq (q x) (r x) / 2)
        = ∑ x, (c x - c x * hellingerSq (q x) (r x) / 2) :=
          Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ x, c x - (∑ x, c x * hellingerSq (q x) (r x)) / 2 := by
          rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ = 1 - E / 2 := by rw [hc.2]
  rw [h4]
  have h5 := Real.add_one_le_exp (-(E / 2))
  have h6 : (1 - E / 2) * Real.exp (E / 2) ≤ Real.exp (-(E / 2)) * Real.exp (E / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add] at h6
  simpa using h6

theorem hel35_alg (c a b E : ℝ) (ha : 0 < a) (hb : 0 < b) :
    c * Real.sqrt (a * b) * Real.exp E =
      (c * b) * Real.exp (-(1 / 2) * (-Real.log a - -Real.log b)) * Real.exp E := by
  have h1 : Real.exp (-(1 / 2) * (-Real.log a - -Real.log b)) = Real.sqrt a / Real.sqrt b := by
    have : -(1 / 2) * (-Real.log a - -Real.log b) = Real.log a * (1 / 2) - Real.log b * (1 / 2) := by
      ring
    rw [this, Real.exp_sub, ← Real.rpow_def_of_pos ha, ← Real.rpow_def_of_pos hb,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [h1, Real.sqrt_mul ha.le]
  have hsb := Real.sqrt_pos.2 hb
  have hb2 := Real.mul_self_sqrt hb.le
  have h3 : b * (Real.sqrt a / Real.sqrt b) = Real.sqrt a * Real.sqrt b := by
    calc b * (Real.sqrt a / Real.sqrt b)
        = (Real.sqrt b * Real.sqrt b) * (Real.sqrt a / Real.sqrt b) := by rw [hb2]
      _ = Real.sqrt a * Real.sqrt b := by field_simp
  calc c * (Real.sqrt a * Real.sqrt b) * Real.exp E
      = c * (b * (Real.sqrt a / Real.sqrt b)) * Real.exp E := by rw [h3]
    _ = c * b * (Real.sqrt a / Real.sqrt b) * Real.exp E := by ring

open StatComplexityDM.Estimation Classical in
theorem solution
    {I X Y : Type*} [Fintype I] [Nonempty I] [Fintype X] [Fintype Y] {T : ℕ}
    (ctx : ContextKernel X Y T) (ghat : Predictor X Y T)
    (g : Experts I X Y T) (istar : I)
    (hctx : IsContextKernel ctx) (hghat : IsPredictor ghat)
    (hg : IsExperts g) (hpos : PositiveOnSupport ctx ghat g istar)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    (∑ h : Hist (X × Y) T,
      if regKL ghat g h + 2 * Real.log (1 / δ) < estH ctx ghat g istar h
      then law ctx g istar h else 0) ≤ δ := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨w, hw⟩ : ∃ w : (t : Fin T) → Hist (X × Y) t.val → X × Y → ℝ,
      w = fun t p xy => ctx t p xy.1 * Real.sqrt (ghat t p xy.1 xy.2 * g istar t p xy.1 xy.2) *
        Real.exp ((∑ x, ctx t p x * FoundationsRL.GeneralDM.hellingerSq (ghat t p x)
          (g istar t p x)) / 2) := ⟨_, rfl⟩
  have hw0 : ∀ t p z, 0 ≤ w t p z := fun t p z => by
    rw [hw]
    exact mul_nonneg (mul_nonneg ((hctx t p).1 _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hw1 : ∀ t p, ∑ z, w t p z ≤ 1 := fun t p => by
    rw [hw]
    exact hel35_step (ctx t p) (ghat t p) (g istar t p) (hctx t p) (fun x => hghat t p x)
      (fun x => hg istar t p x)
  have hprod := hel35_prod_le_one T w hw0 hw1
  have key : ∀ h : Hist (X × Y) T,
      (if regKL ghat g h + 2 * Real.log (1 / δ) < estH ctx ghat g istar h
        then law ctx g istar h else 0) ≤ δ * ∏ t, w t (histPrefix h t) (h t) := by
    intro h
    have hlaw0 : 0 ≤ law ctx g istar h :=
      Finset.prod_nonneg (fun t _ => mul_nonneg ((hctx _ _).1 _) ((hg istar _ _ _).1 _))
    have hprod0 : 0 ≤ ∏ t, w t (histPrefix h t) (h t) :=
      Finset.prod_nonneg (fun t _ => hw0 _ _ _)
    split_ifs with hbad
    · rcases hlaw0.eq_or_lt with hz | hp
      · rw [← hz]; positivity
      · have hpp := hpos h hp
        have hstep : ∀ t, w t (histPrefix h t) (h t) =
            (ctx t (histPrefix h t) (h t).1 * g istar t (histPrefix h t) (h t).1 (h t).2) *
            Real.exp (-(1 / 2) * (logLoss (ghat t (histPrefix h t)) (h t).1 (h t).2 -
              logLoss (g istar t (histPrefix h t)) (h t).1 (h t).2)) *
            Real.exp ((∑ x, ctx t (histPrefix h t) x *
              FoundationsRL.GeneralDM.hellingerSq (ghat t (histPrefix h t) x)
                (g istar t (histPrefix h t) x)) / 2) := by
          intro t
          rw [hw]
          simp only [logLoss]
          exact hel35_alg _ _ _ _ (hpp istar t).2 (hpp istar t).1
        set gap : ℝ := ∑ t, (logLoss (ghat t (histPrefix h t)) (h t).1 (h t).2 -
              logLoss (g istar t (histPrefix h t)) (h t).1 (h t).2) with hgapdef
        have hP : ∏ t, w t (histPrefix h t) (h t) =
            law ctx g istar h * Real.exp ((estH ctx ghat g istar h - gap) / 2) := by
          rw [Finset.prod_congr rfl (fun t _ => hstep t), Finset.prod_mul_distrib,
            Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum]
          have hs1 : ∑ t, -(1 / 2) * (logLoss (ghat t (histPrefix h t)) (h t).1 (h t).2 -
              logLoss (g istar t (histPrefix h t)) (h t).1 (h t).2) = -(1 / 2) * gap := by
            rw [hgapdef, Finset.mul_sum]
          have hs2 : ∑ t, (∑ x, ctx t (histPrefix h t) x *
              FoundationsRL.GeneralDM.hellingerSq (ghat t (histPrefix h t) x)
                (g istar t (histPrefix h t) x)) / 2 = estH ctx ghat g istar h / 2 := by
            unfold estH; rw [Finset.sum_div]
          rw [hs1, hs2, mul_assoc, ← Real.exp_add]
          have : -(1 / 2) * gap + estH ctx ghat g istar h / 2 = (estH ctx ghat g istar h - gap) / 2 := by
            ring
          rw [this]
          rfl
        have hgap : gap ≤ regKL ghat g h := by
          unfold regKL
          have h1 : (Finset.univ : Finset I).inf' Finset.univ_nonempty
              (fun i => ∑ t, logLoss (g i t (histPrefix h t)) (h t).1 (h t).2) ≤
              ∑ t, logLoss (g istar t (histPrefix h t)) (h t).1 (h t).2 :=
            Finset.inf'_le _ (Finset.mem_univ istar)
          rw [hgapdef, Finset.sum_sub_distrib]
          linarith
        have hexp : 1 / δ < Real.exp ((estH ctx ghat g istar h - gap) / 2) := by
          have h2 : Real.log (1 / δ) < (estH ctx ghat g istar h - gap) / 2 := by linarith
          have := Real.exp_lt_exp.2 h2
          rwa [Real.exp_log (by positivity)] at this
        have h3 : 1 < δ * Real.exp ((estH ctx ghat g istar h - gap) / 2) := by
          have := (div_lt_iff₀ hδ0).1 hexp
          linarith
        rw [hP]
        nlinarith
    · positivity
  calc _ ≤ ∑ h : Hist (X × Y) T, δ * ∏ t, w t (histPrefix h t) (h t) :=
        Finset.sum_le_sum (fun h _ => key h)
    _ = δ * ∑ h : Hist (X × Y) T, ∏ t, w t (histPrefix h t) (h t) := by rw [Finset.mul_sum]
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hprod hδ0.le
    _ = δ := mul_one _
