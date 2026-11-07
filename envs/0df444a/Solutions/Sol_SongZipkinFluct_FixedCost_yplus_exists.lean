-- Prove2me | solution 1 for SongZipkinFluct.FixedCost.yplus_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:01:16.097182+00:00
-- url     : https://prove2.me/submissions/66b6be03-67c3-4096-971b-8a448f1fd105

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open MeasureTheory Filter Finset
set_option linter.unusedSectionVars false

namespace SZFYP
open SongZipkinFluct.FixedCost SongZipkinFluct.FixedCost.Model

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

lemma qrate_nonneg (hM : M.Standing) (i : I) : 0 ≤ M.qrate i :=
  (hM.conservative i).nonneg (fun j => by
    split_ifs with h
    · exact le_rfl
    · exact hM.offdiag_nonneg i j h)

lemma rate_le (hM : M.Standing) (i : I) : M.lam i + M.qrate i ≤ M.μ := by
  have h1 : M.lam i ≤ ⨆ i, M.lam i := le_ciSup hM.lam_bdd i
  have h2 : M.qrate i ≤ ⨆ i, M.qrate i := le_ciSup hM.q_bdd i
  linarith [hM.μ_ge]

/-- the inductive invariant of the uniformized chain -/
def Inv (u : I → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i d, 0 ≤ u i d) ∧ (∀ i d, n < d → u i d = 0) ∧ (∀ i, ∑ d ∈ range (n + 1), u i d = 1)

lemma Inv.le_one {u : I → ℕ → ℝ} {n : ℕ} (h : Inv u n) (i : I) (d : ℕ) : u i d ≤ 1 := by
  by_cases hd : n < d
  · rw [h.2.1 i d hd]; norm_num
  · rw [← h.2.2 i]
    exact single_le_sum (fun k _ => h.1 i k) (mem_range.2 (by omega))

lemma jterm_summable (hM : M.Standing) {u : I → ℕ → ℝ} {n : ℕ} (h : Inv u n) (i : I) (d : ℕ) :
    Summable (fun j => if j = i then 0 else M.Q i j / M.μ * u j d) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((hM.conservative i).summable.div_const M.μ)
  · split_ifs with hj
    · exact le_rfl
    · exact mul_nonneg (div_nonneg (hM.offdiag_nonneg i j hj) hM.μ_pos.le) (h.1 j d)
  · split_ifs with hj
    · simp
    · have := h.le_one j d
      have h0 := div_nonneg (hM.offdiag_nonneg i j hj) hM.μ_pos.le
      calc M.Q i j / M.μ * u j d ≤ M.Q i j / M.μ * 1 := mul_le_mul_of_nonneg_left this h0
        _ = M.Q i j / M.μ := mul_one _

lemma inv_step (hM : M.Standing) {u : I → ℕ → ℝ} {n : ℕ} (h : Inv u n) :
    Inv (M.uStep u) (n + 1) := by
  have hμ := hM.μ_pos
  have hc : ∀ i, 0 ≤ 1 - (M.lam i + M.qrate i) / M.μ := fun i => by
    rw [sub_nonneg, div_le_one hμ]; exact rate_le M hM i
  refine ⟨fun i d => ?_, fun i d hd => ?_, fun i => ?_⟩
  · unfold uStep
    refine add_nonneg (add_nonneg ?_ (tsum_nonneg fun j => ?_)) (mul_nonneg (hc i) (h.1 i d))
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (div_nonneg (hM.lam_nonneg i) hμ.le) (h.1 i _)
    · split_ifs with hj
      · exact le_rfl
      · exact mul_nonneg (div_nonneg (hM.offdiag_nonneg i j hj) hμ.le) (h.1 j d)
  · unfold uStep
    have h1 : (if d = 0 then 0 else M.lam i / M.μ * u i (d - 1)) = 0 := by
      split_ifs
      · rfl
      · rw [h.2.1 i (d - 1) (by omega), mul_zero]
    have h2 : (∑' j, if j = i then 0 else M.Q i j / M.μ * u j d) = 0 := by
      have : (fun j => if j = i then 0 else M.Q i j / M.μ * u j d) = fun _ => 0 := by
        funext j; split_ifs
        · rfl
        · rw [h.2.1 j d (by omega), mul_zero]
      rw [this, tsum_zero]
    rw [h1, h2, h.2.1 i d (by omega)]; ring
  · unfold uStep
    rw [sum_add_distrib, sum_add_distrib]
    have e1 : ∑ d ∈ range (n + 1 + 1), (if d = 0 then 0 else M.lam i / M.μ * u i (d - 1))
        = M.lam i / M.μ := by
      rw [sum_range_succ']
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, add_zero]
      rw [← mul_sum, h.2.2 i, mul_one]
    have e3 : ∑ d ∈ range (n + 1 + 1), (1 - (M.lam i + M.qrate i) / M.μ) * u i d
        = 1 - (M.lam i + M.qrate i) / M.μ := by
      rw [← mul_sum, sum_range_succ, h.2.2 i, h.2.1 i (n + 1) (by omega), add_zero, mul_one]
    have e2 : ∑ d ∈ range (n + 1 + 1), (∑' j, if j = i then 0 else M.Q i j / M.μ * u j d)
        = M.qrate i / M.μ := by
      rw [← Summable.tsum_finsetSum (fun d _ => jterm_summable M hM h i d)]
      have : (fun j => ∑ d ∈ range (n + 1 + 1), if j = i then (0:ℝ) else M.Q i j / M.μ * u j d)
          = fun j => (if j = i then 0 else M.Q i j) / M.μ := by
        funext j
        split_ifs with hj
        · simp
        · rw [← mul_sum, sum_range_succ, h.2.2 j, h.2.1 j (n + 1) (by omega), add_zero, mul_one]
      rw [this, ((hM.conservative i).div_const M.μ).tsum_eq]
    rw [e1, e2, e3]; field_simp; ring

lemma inv_all (hM : M.Standing) (n : ℕ) : Inv (M.demandSteps n) n := by
  induction n with
  | zero =>
    refine ⟨fun i d => ?_, fun i d hd => ?_, fun i => ?_⟩
    · simp only [demandSteps]; split_ifs <;> norm_num
    · simp only [demandSteps]; rw [if_neg (by omega)]
    · simp [demandSteps]
  | succ n ih => exact inv_step M hM ih


/-- Poisson weights -/
noncomputable def w (n : ℕ) (l : ℝ) : ℝ :=
  Real.exp (-M.μ * l) * (M.μ * l) ^ n / (n.factorial : ℝ)

lemma w_nonneg (hM : M.Standing) {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : 0 ≤ w M n l := by
  unfold w; have := hM.μ_pos; positivity

lemma w_hasSum (hM : M.Standing) {l : ℝ} (hl : 0 ≤ l) : HasSum (fun n => w M n l) 1 := by
  have := ProbabilityTheory.hasSum_one_poissonMeasure ⟨M.μ * l, mul_nonneg hM.μ_pos.le hl⟩
  convert this using 2 with n
  simp only [w, neg_mul]
  rfl

lemma w_mean (hM : M.Standing) {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun n : ℕ => (n : ℝ) * w M n l) (M.μ * l) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have := (w_hasSum M hM hl).mul_left (M.μ * l)
  rw [mul_one] at this
  have e : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * w M (k + 1) l) = fun k => M.μ * l * w M k l := by
    funext k
    simp only [w, Nat.factorial_succ, Nat.cast_mul, pow_succ, Nat.cast_add, Nat.cast_one]
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e]; exact this

lemma double (F : ℕ → ℕ → ℝ) (h0 : ∀ n d, 0 ≤ F n d) (hsupp : ∀ n d, n < d → F n d = 0)
    (hrow : Summable (fun n => ∑ d ∈ range (n + 1), F n d)) :
    HasSum (fun d => ∑' n, F n d) (∑' n, ∑ d ∈ range (n + 1), F n d) := by
  have hrs : ∀ n, Summable (fun d => F n d) := fun n =>
    summable_of_ne_finset_zero (s := range (n + 1)) (fun d hd => hsupp n d (by simpa using hd))
  have hrt : ∀ n, ∑' d, F n d = ∑ d ∈ range (n + 1), F n d := fun n =>
    tsum_eq_sum (fun d hd => hsupp n d (by simpa using hd))
  have hG : Summable (fun p : ℕ × ℕ => F p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => h0 p.1 p.2)).2 ⟨hrs, by simpa [hrt] using hrow⟩
  have hGs := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => F p.2 p.1)
    (fun p => h0 p.2 p.1)).1 hG.prod_symm
  have hcomm := Summable.tsum_comm' (f := F) hG hrs hGs.1
  rw [← funext hrt, ← hcomm]
  exact hGs.2.hasSum

lemma dm_eq (i : I) (d : ℕ) (l : ℝ) :
    M.demandMass i d l = ∑' n, w M n l * M.demandSteps n i d := rfl

lemma dm_nonneg (hM : M.Standing) (i : I) (d : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    0 ≤ M.demandMass i d l :=
  tsum_nonneg fun n => mul_nonneg (w_nonneg M hM hl n) ((inv_all M hM n).1 i d)

lemma dm_hasSum (hM : M.Standing) (i : I) {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun d => M.demandMass i d l) 1 := by
  have := double (fun n d => w M n l * M.demandSteps n i d)
    (fun n d => mul_nonneg (w_nonneg M hM hl n) ((inv_all M hM n).1 i d))
    (fun n d h => by rw [(inv_all M hM n).2.1 i d h, mul_zero])
    (by simpa [← mul_sum, (inv_all M hM _).2.2 i] using (w_hasSum M hM hl).summable)
  simp only [← mul_sum, (inv_all M hM _).2.2 i, mul_one, (w_hasSum M hM hl).tsum_eq] at this
  exact this

lemma dm_mean (hM : M.Standing) (i : I) {l : ℝ} (hl : 0 ≤ l) :
    Summable (fun d : ℕ => (d : ℝ) * M.demandMass i d l) ∧
      ∑' d : ℕ, (d : ℝ) * M.demandMass i d l ≤ M.μ * l := by
  have hrowle : ∀ n, ∑ d ∈ range (n + 1), (d : ℝ) * (w M n l * M.demandSteps n i d)
      ≤ (n : ℝ) * w M n l := by
    intro n
    calc ∑ d ∈ range (n + 1), (d : ℝ) * (w M n l * M.demandSteps n i d)
        ≤ ∑ d ∈ range (n + 1), (n : ℝ) * (w M n l * M.demandSteps n i d) := by
          refine sum_le_sum fun d hd => mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (w_nonneg M hM hl n) ((inv_all M hM n).1 i d))
          have := mem_range.1 hd; exact_mod_cast (by omega : d ≤ n)
      _ = (n : ℝ) * w M n l := by rw [← mul_sum, ← mul_sum, (inv_all M hM n).2.2 i, mul_one]
  have hnn : ∀ n d : ℕ, 0 ≤ (d : ℝ) * (w M n l * M.demandSteps n i d) := fun n d =>
    mul_nonneg d.cast_nonneg (mul_nonneg (w_nonneg M hM hl n) ((inv_all M hM n).1 i d))
  have hrow : Summable (fun n => ∑ d ∈ range (n + 1), (d : ℝ) * (w M n l * M.demandSteps n i d)) :=
    Summable.of_nonneg_of_le (fun n => sum_nonneg fun d _ => hnn n d) hrowle (w_mean M hM hl).summable
  have := double (fun n d : ℕ => (d : ℝ) * (w M n l * M.demandSteps n i d)) hnn
    (fun n d h => by rw [(inv_all M hM n).2.1 i d h, mul_zero, mul_zero]) hrow
  have heq : (fun d : ℕ => ∑' n, (d : ℝ) * (w M n l * M.demandSteps n i d))
      = fun d : ℕ => (d : ℝ) * M.demandMass i d l := by
    funext d; rw [dm_eq, tsum_mul_left]
  rw [heq] at this
  refine ⟨this.summable, ?_⟩
  rw [this.tsum_eq, ← (w_mean M hM hl).tsum_eq]
  exact Summable.tsum_le_tsum hrowle hrow (w_mean M hM hl).summable

lemma dm_measurable (hM : M.Standing) (i : I) (d : ℕ) : Measurable (M.demandMass i d) := by
  have hs : ∀ l, Summable (fun n => w M n l * M.demandSteps n i d) := by
    intro l
    refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial (|M.μ * l|)).mul_left (Real.exp (-M.μ * l))) fun n => ?_
    have h1 := (inv_all M hM n).1 i d
    have h2 := (inv_all M hM n).le_one i d
    rw [Real.norm_eq_abs, abs_mul]
    calc |w M n l| * |M.demandSteps n i d| ≤ |w M n l| * 1 := by
          gcongr; rw [abs_of_nonneg h1]; exact h2
      _ = Real.exp (-M.μ * l) * (|M.μ * l| ^ n / (n.factorial : ℝ)) := by
          rw [mul_one, w, abs_div, abs_mul, abs_pow, Real.abs_exp, Nat.abs_cast]; ring
  refine measurable_of_tendsto_metrizable
    (f := fun N l => ∑ n ∈ range N, w M n l * M.demandSteps n i d) (fun N => ?_) ?_
  · unfold w; fun_prop
  · exact tendsto_pi_nhds.2 fun l => (hs l).hasSum.tendsto_sum_nat


lemma summable_of_ennreal {f : ℕ → ℝ} (h0 : ∀ d, 0 ≤ f d)
    (h : ∑' d, ENNReal.ofReal (f d) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal h
  simpa [ENNReal.toReal_ofReal (h0 _)] using this

lemma hasSum_of_ennreal {f : ℕ → ℝ} (h0 : ∀ d, 0 ≤ f d) {a : ℝ} (ha : 0 ≤ a)
    (h : ∑' d, ENNReal.ofReal (f d) = ENNReal.ofReal a) : HasSum f a := by
  have hs : Summable f := summable_of_ennreal h0 (by rw [h]; exact ENNReal.ofReal_ne_top)
  have e := ENNReal.ofReal_tsum_of_nonneg h0 hs
  rw [h, ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg h0) ha] at e
  rw [← e]; exact hs.hasSum

lemma dm_le_one (hM : M.Standing) (i : I) (d : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    M.demandMass i d l ≤ 1 :=
  le_hasSum (dm_hasSum M hM i hl) d (fun j _ => dm_nonneg M hM i j hl)

lemma Phi_meas (hM : M.Standing) (i : I) (d : ℕ) :
    Measurable (fun l => Real.exp (-M.α * l) * M.demandMass i d l) := by
  have := dm_measurable M hM i d
  fun_prop

lemma exp_integrable (hM : M.Standing) :
    Integrable (fun l => Real.exp (-M.α * l)) M.leadLaw := by
  have := hM.lead_prob
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hM.lead_nonneg] with l hl
  rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
  nlinarith [hM.α_pos]

lemma Phi_integrable (hM : M.Standing) (i : I) (d : ℕ) :
    Integrable (fun l => Real.exp (-M.α * l) * M.demandMass i d l) M.leadLaw := by
  refine (exp_integrable M hM).mono' (Phi_meas M hM i d).aestronglyMeasurable ?_
  filter_upwards [hM.lead_nonneg] with l hl
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_of_nonneg (dm_nonneg M hM i d hl)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (dm_le_one M hM i d hl)

lemma g_nonneg (hM : M.Standing) (i : I) (d : ℕ) : 0 ≤ M.discDemandMass i d := by
  unfold discDemandMass
  refine integral_nonneg_of_ae ?_
  filter_upwards [hM.lead_nonneg] with l hl
  exact mul_nonneg (Real.exp_pos _).le (dm_nonneg M hM i d hl)

lemma lapL_pos (hM : M.Standing) : 0 < M.lapL := by
  have := hM.lead_prob
  exact integral_exp_pos (exp_integrable M hM)

lemma g_hasSum (hM : M.Standing) (i : I) : HasSum (M.discDemandMass i) M.lapL := by
  refine hasSum_of_ennreal (g_nonneg M hM i) (lapL_pos M hM).le ?_
  have e1 : ∀ d, ENNReal.ofReal (M.discDemandMass i d)
      = ∫⁻ l, ENNReal.ofReal (Real.exp (-M.α * l) * M.demandMass i d l) ∂M.leadLaw := by
    intro d
    refine ofReal_integral_eq_lintegral_ofReal (Phi_integrable M hM i d) ?_
    filter_upwards [hM.lead_nonneg] with l hl
    exact mul_nonneg (Real.exp_pos _).le (dm_nonneg M hM i d hl)
  simp_rw [e1]
  rw [← lintegral_tsum (fun d => (Phi_meas M hM i d).ennreal_ofReal.aemeasurable), lapL,
    ofReal_integral_eq_lintegral_ofReal (exp_integrable M hM)
      (Eventually.of_forall fun l => (Real.exp_pos _).le)]
  refine lintegral_congr_ae ?_
  filter_upwards [hM.lead_nonneg] with l hl
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun d => mul_nonneg (Real.exp_pos _).le (dm_nonneg M hM i d hl))
    ((dm_hasSum M hM i hl).summable.mul_left _), tsum_mul_left, (dm_hasSum M hM i hl).tsum_eq,
    mul_one]

lemma g_mean (hM : M.Standing) (i : I) :
    Summable (fun d : ℕ => (d : ℝ) * M.discDemandMass i d) := by
  have := hM.lead_prob
  refine summable_of_ennreal (fun d => mul_nonneg d.cast_nonneg (g_nonneg M hM i d)) ?_
  have e1 : ∀ d : ℕ, ENNReal.ofReal ((d : ℝ) * M.discDemandMass i d)
      = ∫⁻ l, ENNReal.ofReal ((d : ℝ) * (Real.exp (-M.α * l) * M.demandMass i d l))
        ∂M.leadLaw := by
    intro d
    rw [discDemandMass, ← integral_const_mul]
    refine ofReal_integral_eq_lintegral_ofReal ((Phi_integrable M hM i d).const_mul _) ?_
    filter_upwards [hM.lead_nonneg] with l hl
    exact mul_nonneg d.cast_nonneg (mul_nonneg (Real.exp_pos _).le (dm_nonneg M hM i d hl))
  simp_rw [e1]
  rw [← lintegral_tsum (fun d => ((Phi_meas M hM i d).const_mul _).ennreal_ofReal.aemeasurable)]
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (M.μ / M.α)) ?_)
    (by simp))
  filter_upwards [hM.lead_nonneg] with l hl
  have hm := dm_mean M hM i hl
  have hnn : ∀ d : ℕ, 0 ≤ (d : ℝ) * (Real.exp (-M.α * l) * M.demandMass i d l) := fun d =>
    mul_nonneg d.cast_nonneg (mul_nonneg (Real.exp_pos _).le (dm_nonneg M hM i d hl))
  have hs : Summable (fun d : ℕ => (d : ℝ) * (Real.exp (-M.α * l) * M.demandMass i d l)) := by
    have := hm.1.mul_left (Real.exp (-M.α * l))
    refine this.congr fun d => by ring
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ∑' d : ℕ, (d : ℝ) * (Real.exp (-M.α * l) * M.demandMass i d l)
      = Real.exp (-M.α * l) * ∑' d : ℕ, (d : ℝ) * M.demandMass i d l := by
    rw [← tsum_mul_left]; congr 1; funext d; ring
  rw [this]
  have hα := hM.α_pos
  have hμ := hM.μ_pos
  have hexp := Real.add_one_le_exp (M.α * l)
  have hpos := Real.exp_pos (M.α * l)
  have hinv : Real.exp (-M.α * l) * Real.exp (M.α * l) = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hα]
  calc (Real.exp (-M.α * l) * ∑' d : ℕ, (d : ℝ) * M.demandMass i d l) * M.α
      ≤ Real.exp (-M.α * l) * (M.μ * l) * M.α := by
        gcongr; exact hm.2
    _ = M.μ * (Real.exp (-M.α * l) * (M.α * l)) := by ring
    _ ≤ M.μ * (Real.exp (-M.α * l) * Real.exp (M.α * l)) := by gcongr; linarith
    _ = M.μ := by rw [hinv, mul_one]


lemma Chat_nonpos (x : ℝ) (hx : x ≤ 0) : M.Chat x = -M.p * x := by
  unfold Chat
  split_ifs with h
  · rfl
  · have : x = 0 := le_antisymm hx (not_lt.1 h)
    subst this; simp

lemma Chat_ge (hM : M.Standing) (x : ℝ) : M.h * x ≤ M.Chat x := by
  unfold Chat
  split_ifs with h
  · nlinarith [hM.h_pos, hM.p_pos]
  · exact le_rfl

lemma Chat_abs (hM : M.Standing) (x : ℝ) : |M.Chat x| ≤ (M.h + M.p) * |x| := by
  unfold Chat
  have := hM.h_pos; have := hM.p_pos
  split_ifs
  · rw [abs_mul, abs_neg, abs_of_pos hM.p_pos]; nlinarith [abs_nonneg x]
  · rw [abs_mul, abs_of_pos hM.h_pos]; nlinarith [abs_nonneg x]

lemma C_nonpos (hM : M.Standing) (i : I) (y : ℤ) (hy : y ≤ 0) :
    M.C i y = M.p * (∑' d : ℕ, (d : ℝ) * M.discDemandMass i d) - M.p * y * M.lapL := by
  have h := ((g_mean M hM i).hasSum.mul_left M.p).sub ((g_hasSum M hM i).mul_left (M.p * y))
  rw [C, ← h.tsum_eq]
  congr 1; funext d
  have : ((y : ℝ) - (d : ℝ)) ≤ 0 := by
    have : (y : ℝ) ≤ 0 := by exact_mod_cast hy
    linarith [d.cast_nonneg (α := ℝ)]
  rw [Chat_nonpos M _ this]; ring

lemma C_lower (hM : M.Standing) (i : I) (y : ℤ) :
    M.h * (y * M.lapL - ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d) ≤ M.C i y := by
  have h := ((g_hasSum M hM i).mul_left (M.h * y)).sub ((g_mean M hM i).hasSum.mul_left M.h)
  have hs : Summable (fun d : ℕ => M.discDemandMass i d * M.Chat ((y : ℝ) - (d : ℝ))) := by
    refine Summable.of_norm_bounded
      ((((g_hasSum M hM i).summable.mul_left ((M.h + M.p) * |(y : ℝ)|))).add
        ((g_mean M hM i).mul_left (M.h + M.p))) fun d => ?_
    have hg := g_nonneg M hM i d
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
    have h1 := Chat_abs M hM ((y : ℝ) - (d : ℝ))
    have h2 : |(y : ℝ) - (d : ℝ)| ≤ |(y : ℝ)| + d := by
      calc |(y : ℝ) - (d : ℝ)| ≤ |(y : ℝ)| + |(d : ℝ)| := abs_sub _ _
        _ = |(y : ℝ)| + d := by rw [Nat.abs_cast]
    have := hM.h_pos; have := hM.p_pos
    calc M.discDemandMass i d * |M.Chat (↑y - ↑d)|
        ≤ M.discDemandMass i d * ((M.h + M.p) * (|(y : ℝ)| + d)) := by
          gcongr; exact h1.trans (by gcongr)
      _ = _ := by ring
  rw [mul_sub, ← mul_assoc, ← h.tsum_eq, C]
  refine Summable.tsum_le_tsum (fun d => ?_) h.summable hs
  have := Chat_ge M hM ((y : ℝ) - (d : ℝ))
  have hg := g_nonneg M hM i d
  nlinarith

lemma one_sub_gamma (hM : M.Standing) : 1 - M.γ = M.α * M.β := by
  have := hM.μ_pos; have := hM.α_pos
  unfold γ β; field_simp; ring

lemma beta_pos (hM : M.Standing) : 0 < M.β := by
  unfold β; have := hM.μ_pos; have := hM.α_pos; positivity

lemma Gplus_neg (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) (y : ℤ) (hy : y < 0) :
    M.Gplus i 0 < M.Gplus i y := by
  unfold Gplus
  rw [C_nonpos M hM i y hy.le, C_nonpos M hM i 0 le_rfl, one_sub_gamma M hM, c]
  have hb := beta_pos M hM
  have hl := lapL_pos M hM
  have hy' : (y : ℝ) < 0 := by exact_mod_cast hy
  have : 0 < M.β * M.lapL * (M.p - M.α * M.cbar) := by
    have : 0 < M.p - M.α * M.cbar := by linarith
    positivity
  push_cast
  nlinarith

lemma Gplus_big (hM : M.Standing) (i : I) : ∃ Y : ℤ, 0 ≤ Y ∧ ∀ y, Y ≤ y → M.Gplus i 0 < M.Gplus i y := by
  set m := ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d
  have hb := beta_pos M hM
  have hl := lapL_pos M hM
  have hh := hM.h_pos
  obtain ⟨Y, hY⟩ := exists_int_gt ((M.Gplus i 0 / (M.β * M.h) + m) / M.lapL)
  refine ⟨max Y 0, le_max_right _ _, fun y hy => ?_⟩
  have hy0 : (0 : ℝ) ≤ y := by exact_mod_cast (le_max_right Y 0).trans hy
  have hyY : (Y : ℝ) ≤ y := by exact_mod_cast (le_max_left Y 0).trans hy
  have hlow := C_lower M hM i y
  have hc : 0 ≤ (1 - M.γ) * M.c * y := by
    rw [one_sub_gamma M hM, c]
    have := hM.cbar_nonneg; have := hM.α_pos
    positivity
  have h1 : M.Gplus i 0 / (M.β * M.h) + m < y * M.lapL := by
    rw [div_lt_iff₀ hl] at hY; nlinarith
  have h2 : M.Gplus i 0 < M.β * M.h * (y * M.lapL - m) := by
    rw [div_add' _ _ _ (by positivity), div_lt_iff₀ (by positivity)] at h1; nlinarith
  unfold Gplus at h2 ⊢
  nlinarith

theorem main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    (∃ yplus, IsYPlus M yplus) ∧ ∀ yplus, IsYPlus M yplus → ∃ ymin, IsYPlusMin yplus ymin := by
  have hex : ∀ i, ∃ y, IsSmallestMin (M.Gplus i) y := by
    intro i
    obtain ⟨Y, hY0, hY⟩ := Gplus_big M hM i
    obtain ⟨y0, hy0, hmin⟩ := (Finset.Icc (0 : ℤ) Y).exists_min_image (M.Gplus i)
      ⟨0, Finset.mem_Icc.2 ⟨le_rfl, hY0⟩⟩
    have h0 := hmin 0 (Finset.mem_Icc.2 ⟨le_rfl, hY0⟩)
    have hglob : ∀ w, M.Gplus i y0 ≤ M.Gplus i w := by
      intro w
      by_cases hw : w < 0
      · exact h0.trans (Gplus_neg M hM hA1 i w hw).le
      by_cases hw' : Y ≤ w
      · exact h0.trans (hY w hw').le
      · exact hmin w (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    obtain ⟨lb, hlb, hlbmin⟩ := Int.exists_least_of_bdd
      (P := fun z => ∀ w, M.Gplus i z ≤ M.Gplus i w)
      ⟨0, fun z hz => by
        by_contra h
        exact absurd (hz 0) (not_le.2 (Gplus_neg M hM hA1 i z (by omega)))⟩ ⟨y0, hglob⟩
    exact ⟨lb, hlb, fun z hz => hlbmin z hz⟩
  choose yp hyp using hex
  refine ⟨⟨yp, hyp⟩, fun yplus hy => ?_⟩
  have hnn : ∀ i, 0 ≤ yplus i := by
    intro i
    by_contra h
    exact absurd ((hy i).1 0) (not_le.2 (Gplus_neg M hM hA1 i _ (by omega)))
  obtain ⟨lb, ⟨j, hj⟩, hlb⟩ := Int.exists_least_of_bdd (P := fun z => z ∈ Set.range yplus)
    ⟨0, fun z ⟨i, hi⟩ => hi ▸ hnn i⟩ ⟨yplus (Classical.arbitrary I), ⟨_, rfl⟩⟩
  exact ⟨lb, ⟨j, hj⟩, fun z hz => hlb z hz⟩

end SZFYP

open SongZipkinFluct.FixedCost in
theorem solution {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    (∃ yplus, IsYPlus M yplus) ∧ ∀ yplus, IsYPlus M yplus → ∃ ymin, IsYPlusMin yplus ymin :=
  SZFYP.main M hM hA1
