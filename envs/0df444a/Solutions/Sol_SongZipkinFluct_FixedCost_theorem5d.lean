-- Prove2me | solution 1 for SongZipkinFluct.FixedCost.theorem5d
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:19:42.080206+00:00
-- url     : https://prove2.me/submissions/00b5ed25-8c6f-455f-8c1f-195ba19c1f89

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open MeasureTheory Filter Finset Topology
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


lemma C_nonneg (hM : M.Standing) (i : I) (y : ℤ) : 0 ≤ M.C i y := by
  refine tsum_nonneg fun d => mul_nonneg (g_nonneg M hM i d) ?_
  unfold Chat; have := hM.h_pos; have := hM.p_pos
  split_ifs with h <;> nlinarith

lemma m_nonneg (hM : M.Standing) (i : I) : 0 ≤ ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d :=
  tsum_nonneg fun d => mul_nonneg d.cast_nonneg (g_nonneg M hM i d)

lemma Gplus_nonneg (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) (y : ℤ) :
    0 ≤ M.Gplus i y := by
  have hb := beta_pos M hM
  rcases le_or_gt 0 y with hy | hy
  · unfold Gplus
    have : 0 ≤ (1 - M.γ) * M.c * y := by
      rw [one_sub_gamma M hM, c]
      have := hM.cbar_nonneg; have := hM.α_pos; have := lapL_pos M hM
      have : (0:ℝ) ≤ y := by exact_mod_cast hy
      positivity
    have := C_nonneg M hM i y
    positivity
  · have h0 : 0 ≤ M.Gplus i 0 := by
      unfold Gplus; simp only [Int.cast_zero, mul_zero, zero_add]
      exact mul_nonneg hb.le (C_nonneg M hM i 0)
    exact h0.trans (Gplus_neg M hM hA1 i y hy).le

lemma m_le (hM : M.Standing) (i : I) : ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d ≤ M.μ / M.α := by
  -- re-derive from the ENNReal bound
  have := hM.lead_prob
  have hnn : ∀ d : ℕ, 0 ≤ (d : ℝ) * M.discDemandMass i d :=
    fun d => mul_nonneg d.cast_nonneg (g_nonneg M hM i d)
  have hs := g_mean M hM i
  have hμα : 0 ≤ M.μ / M.α := div_nonneg hM.μ_pos.le hM.α_pos.le
  rw [← ENNReal.ofReal_le_ofReal_iff hμα, ENNReal.ofReal_tsum_of_nonneg hnn hs]
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
  refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal (M.μ / M.α)) ?_).trans (by simp)
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
  have hinv : Real.exp (-M.α * l) * Real.exp (M.α * l) = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hα]
  calc (Real.exp (-M.α * l) * ∑' d : ℕ, (d : ℝ) * M.demandMass i d l) * M.α
      ≤ Real.exp (-M.α * l) * (M.μ * l) * M.α := by
        gcongr; exact hm.2
    _ = M.μ * (Real.exp (-M.α * l) * (M.α * l)) := by ring
    _ ≤ M.μ * (Real.exp (-M.α * l) * Real.exp (M.α * l)) := by gcongr; linarith
    _ = M.μ := by rw [hinv, mul_one]

lemma C_upper (hM : M.Standing) (i : I) (y : ℤ) (hy : 0 ≤ y) :
    M.C i y ≤ (M.h + M.p) * (y * M.lapL + M.μ / M.α) := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have h := ((g_hasSum M hM i).mul_left ((M.h + M.p) * y)).add
    ((g_mean M hM i).hasSum.mul_left (M.h + M.p))
  have hs : Summable (fun d : ℕ => M.discDemandMass i d * M.Chat ((y : ℝ) - (d : ℝ))) := by
    refine Summable.of_norm_bounded h.summable fun d => ?_
    have hg := g_nonneg M hM i d
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
    have h1 := Chat_abs M hM ((y : ℝ) - (d : ℝ))
    have h2 : |(y : ℝ) - (d : ℝ)| ≤ y + d := by
      rw [abs_le]; constructor <;> linarith [d.cast_nonneg (α := ℝ)]
    have := hM.h_pos; have := hM.p_pos
    calc M.discDemandMass i d * |M.Chat (↑y - ↑d)|
        ≤ M.discDemandMass i d * ((M.h + M.p) * (y + d)) := by
          gcongr; exact h1.trans (by gcongr)
      _ = _ := by ring
  have hle : M.C i y ≤ (M.h + M.p) * y * M.lapL + (M.h + M.p) * ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d := by
    rw [← h.tsum_eq, C]
    refine Summable.tsum_le_tsum (fun d => ?_) hs h.summable
    have hg := g_nonneg M hM i d
    have h1 := le_abs_self (M.Chat ((y : ℝ) - (d : ℝ)))
    have h2 := Chat_abs M hM ((y : ℝ) - (d : ℝ))
    have h3 : |(y : ℝ) - (d : ℝ)| ≤ y + d := by
      rw [abs_le]; constructor <;> linarith [d.cast_nonneg (α := ℝ)]
    have := hM.h_pos; have := hM.p_pos
    have : M.Chat ((y : ℝ) - (d : ℝ)) ≤ (M.h + M.p) * (y + d) :=
      h1.trans (h2.trans (by gcongr))
    nlinarith
  have := m_le M hM i
  have := hM.h_pos; have := hM.p_pos
  nlinarith


lemma c_nonneg (hM : M.Standing) : 0 ≤ M.c := mul_nonneg hM.cbar_nonneg (lapL_pos M hM).le

lemma gamma_lt (hM : M.Standing) : 0 < 1 - M.γ := by
  rw [one_sub_gamma M hM]; exact mul_pos hM.α_pos (beta_pos M hM)

lemma gamma_def (hM : M.Standing) : M.γ = M.β * M.μ := rfl

lemma contG_bounds (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (V : ℤ → ℝ) (hV : Monotone V)
    (Wc : I → ℤ → ℝ) (hW : ∀ j y, 0 ≤ Wc j y ∧ Wc j y ≤ V y) (i : I) (y : ℤ) :
    0 ≤ contG M Wc i y ∧
      contG M Wc i y ≤ M.Gplus i y + M.β * (⨆ j, M.lam j) * M.c + M.γ * V y := by
  have hb := beta_pos M hM
  have hc := c_nonneg M hM
  have hl := hM.lam_nonneg i
  have hq := qrate_nonneg M hM i
  have hr := rate_le M hM i
  have hΛ : M.lam i ≤ ⨆ j, M.lam j := le_ciSup hM.lam_bdd i
  have hVy : 0 ≤ V y := (hW i y).1.trans (hW i y).2
  have hf0 : ∀ j, 0 ≤ (if j = i then 0 else M.Q i j * Wc j y) := fun j => by
    split_ifs with hj
    · exact le_rfl
    · exact mul_nonneg (hM.offdiag_nonneg i j hj) (hW j y).1
  have hfle : ∀ j, (if j = i then 0 else M.Q i j * Wc j y) ≤ (if j = i then 0 else M.Q i j) * V y :=
    fun j => by
      split_ifs with hj
      · simp
      · exact mul_le_mul_of_nonneg_left (hW j y).2 (hM.offdiag_nonneg i j hj)
  have hS := (hM.conservative i).mul_right (V y)
  have hsum : Summable (fun j => if j = i then 0 else M.Q i j * Wc j y) :=
    Summable.of_nonneg_of_le hf0 hfle hS.summable
  have hT0 : 0 ≤ (∑' j, if j = i then 0 else M.Q i j * Wc j y) := tsum_nonneg hf0
  have hT1 : (∑' j, if j = i then 0 else M.Q i j * Wc j y) ≤ M.qrate i * V y := by
    rw [← hS.tsum_eq]; exact Summable.tsum_le_tsum hfle hsum hS.summable
  have hGp := Gplus_nonneg M hM hA1 i y
  have hW1 := hW i (y - 1)
  have hW2 := hW i y
  have hVm : V (y - 1) ≤ V y := hV (by omega)
  unfold contG
  constructor
  · have hmq : 0 ≤ M.μ - M.lam i - M.qrate i := by linarith
    have : 0 ≤ M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
        + (M.μ - M.lam i - M.qrate i) * Wc i y := by
      have h1 := mul_nonneg hl hW1.1
      have h2 := mul_nonneg hmq hW2.1
      linarith
    have := mul_nonneg hl hc
    positivity
  · rw [gamma_def M hM]
    have h1 : M.lam i * Wc i (y - 1) ≤ M.lam i * V y :=
      mul_le_mul_of_nonneg_left (hW1.2.trans hVm) hl
    have h3 : (M.μ - M.lam i - M.qrate i) * Wc i y ≤ (M.μ - M.lam i - M.qrate i) * V y :=
      mul_le_mul_of_nonneg_left hW2.2 (by linarith)
    have h4 : M.β * M.lam i * M.c ≤ M.β * (⨆ j, M.lam j) * M.c := by gcongr
    have h5 : M.β * (M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
        + (M.μ - M.lam i - M.qrate i) * Wc i y) ≤ M.β * M.μ * V y := by
      have : M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
          + (M.μ - M.lam i - M.qrate i) * Wc i y ≤ M.μ * V y := by nlinarith
      nlinarith
    linarith

theorem lemma4_main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (K : ℝ) (hK : 0 ≤ K)
    (W₀ : I → ℤ → ℝ) (WB₀ : ℤ → ℝ) (hWB₀ : Monotone WB₀)
    (h11 : ∀ i x, 0 ≤ W₀ i x ∧ W₀ i x ≤ WB₀ x) :
    ∃ WB : ℤ → ℝ, Monotone WB ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i x, 0 ≤ W M K W₀ n i x ∧ W M K W₀ n i x ≤ WB x := by
  set Λ := ⨆ j, M.lam j
  have hb := beta_pos M hM
  have hc := c_nonneg M hM
  have hg := gamma_lt M hM
  have hlap := lapL_pos M hM
  have hhp : 0 ≤ M.h + M.p := by linarith [hM.h_pos, hM.p_pos]
  have hΛ : 0 ≤ Λ := (hM.lam_nonneg (Classical.arbitrary I)).trans (le_ciSup hM.lam_bdd _)
  have hμα : 0 ≤ M.μ / M.α := div_nonneg hM.μ_pos.le hM.α_pos.le
  let a : ℤ → ℝ := fun x => (1 - M.γ) * M.c * (max x 0 : ℤ)
    + M.β * (M.h + M.p) * ((max x 0 : ℤ) * M.lapL + M.μ / M.α) + M.β * Λ * M.c
  have ha0 : ∀ x, 0 ≤ a x := fun x => by
    have : (0 : ℝ) ≤ ((max x 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right x 0
    simp only [a]; positivity
  have ham : Monotone a := by
    intro x y hxy
    have : ((max x 0 : ℤ) : ℝ) ≤ ((max y 0 : ℤ) : ℝ) := by exact_mod_cast max_le_max hxy le_rfl
    simp only [a]; gcongr
  have hWB0 : ∀ x, 0 ≤ WB₀ x := fun x =>
    (h11 (Classical.arbitrary I) x).1.trans (h11 (Classical.arbitrary I) x).2
  let V : ℤ → ℝ := fun x => (K + a x) / (1 - M.γ) + WB₀ (max x 0)
  have hVm : Monotone V := by
    intro x y hxy
    simp only [V]
    have := ham hxy
    have := hWB₀ (max_le_max hxy (le_refl (0:ℤ)))
    gcongr
  refine ⟨V, hVm, ?_⟩
  have key : ∀ n : ℕ, ∀ i x, 0 ≤ W M K W₀ n i x ∧ W M K W₀ n i x ≤ V x := by
    intro n
    induction n with
    | zero =>
      intro i x
      refine ⟨(h11 i x).1, (h11 i x).2.trans ?_⟩
      have : WB₀ x ≤ WB₀ (max x 0) := hWB₀ (le_max_left _ _)
      have : 0 ≤ (K + a x) / (1 - M.γ) := div_nonneg (by linarith [ha0 x]) hg.le
      simp only [V]; linarith
    | succ n ih =>
      intro i x
      have hcb := contG_bounds M hM hA1 V hVm (W M K W₀ n) ih i
      have hδ : ∀ z : ℤ, 0 ≤ SongZipkinFluct.Linear.delta z ∧ SongZipkinFluct.Linear.delta z ≤ 1 :=
        fun z => by unfold SongZipkinFluct.Linear.delta; split_ifs <;> norm_num
      have hterm0 : ∀ y : {y : ℤ // x ≤ y},
          0 ≤ K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M K W₀ n) i y.1 :=
        fun y => add_nonneg (mul_nonneg hK (hδ _).1) (hcb y.1).1
      have hbdd : BddBelow (Set.range fun y : {y : ℤ // x ≤ y} =>
          K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M K W₀ n) i y.1) :=
        ⟨0, by rintro _ ⟨y, rfl⟩; exact hterm0 y⟩
      have hne : Nonempty {y : ℤ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
      show 0 ≤ (⨅ y : {y : ℤ // x ≤ y}, K * SongZipkinFluct.Linear.delta (y.1 - x)
          + contG M (W M K W₀ n) i y.1) ∧ (⨅ y : {y : ℤ // x ≤ y}, K * SongZipkinFluct.Linear.delta (y.1 - x)
          + contG M (W M K W₀ n) i y.1) ≤ V x
      refine ⟨le_ciInf hterm0, (ciInf_le hbdd ⟨max x 0, le_max_left _ _⟩).trans ?_⟩
      simp only
      set x' := max x 0 with hx'
      have hx'0 : 0 ≤ x' := le_max_right _ _
      have hGp : M.Gplus i x' ≤ (1 - M.γ) * M.c * x' + M.β * ((M.h + M.p) * (x' * M.lapL + M.μ / M.α)) := by
        unfold Gplus; gcongr; exact C_upper M hM i x' hx'0
      have hax : a x = (1 - M.γ) * M.c * x' + M.β * (M.h + M.p) * (x' * M.lapL + M.μ / M.α)
          + M.β * Λ * M.c := rfl
      have hVx : V x' = V x := by simp only [V, a, hx', max_eq_left (le_max_right x (0:ℤ))]
      have h2 := (hcb x').2
      rw [hVx] at h2
      have h3 : K * SongZipkinFluct.Linear.delta (x' - x) ≤ K :=
        mul_le_of_le_one_right hK (hδ _).2
      have hVdef : V x = (K + a x) / (1 - M.γ) + WB₀ x' := rfl
      have hfin : K + a x + M.γ * V x ≤ V x := by
        rw [hVdef]
        have hw := hWB0 x'
        have hγ : M.γ ≤ 1 := by linarith
        have e : K + a x + M.γ * ((K + a x) / (1 - M.γ) + WB₀ x')
            = (K + a x) / (1 - M.γ) + M.γ * WB₀ x' := by
          field_simp; ring
        rw [e]
        have hγ0 : 0 ≤ M.γ := by rw [gamma_def M hM]; exact mul_nonneg hb.le hM.μ_pos.le
        nlinarith
      nlinarith
  exact fun n _ => key n


lemma contG_ge (hM : M.Standing) (Wc : I → ℤ → ℝ) (hW : ∀ j y, 0 ≤ Wc j y) (i : I) (y : ℤ) :
    M.Gplus i y ≤ contG M Wc i y := by
  have hb := beta_pos M hM
  have hc := c_nonneg M hM
  have hl := hM.lam_nonneg i
  have hr := rate_le M hM i
  have hf0 : ∀ j, 0 ≤ (if j = i then 0 else M.Q i j * Wc j y) := fun j => by
    split_ifs with hj
    · exact le_rfl
    · exact mul_nonneg (hM.offdiag_nonneg i j hj) (hW j y)
  have hT0 : 0 ≤ (∑' j, if j = i then 0 else M.Q i j * Wc j y) := tsum_nonneg hf0
  have h1 := mul_nonneg hl (hW i (y - 1))
  have h2 := mul_nonneg (by linarith : 0 ≤ M.μ - M.lam i - M.qrate i) (hW i y)
  have h3 : 0 ≤ M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
      + (M.μ - M.lam i - M.qrate i) * Wc i y := by linarith
  have h4 := mul_nonneg hb.le h3
  have h5 := mul_nonneg (mul_nonneg hb.le hl) hc
  unfold contG; linarith

lemma Gplus_far (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) (R : ℝ) :
    ∃ Y : ℤ, 0 ≤ Y ∧ ∀ y, (Y ≤ y ∨ y ≤ -Y) → R < M.Gplus i y := by
  set m := ∑' d : ℕ, (d : ℝ) * M.discDemandMass i d
  have hb := beta_pos M hM
  have hl := lapL_pos M hM
  have hh := hM.h_pos
  have hm := m_nonneg M hM i
  have hs : 0 < M.β * M.lapL * (M.p - M.α * M.cbar) := by
    have : 0 < M.p - M.α * M.cbar := by linarith
    positivity
  obtain ⟨Y1, hY1⟩ := exists_int_gt ((R / (M.β * M.h) + m) / M.lapL)
  obtain ⟨Y2, hY2⟩ := exists_int_gt ((R - M.β * M.p * m) / (M.β * M.lapL * (M.p - M.α * M.cbar)))
  refine ⟨max (max Y1 Y2) 0, le_max_right _ _, fun y hy => ?_⟩
  rcases hy with hy | hy
  · have hy0 : (0 : ℝ) ≤ y := by exact_mod_cast (le_max_right _ 0).trans hy
    have hyY : (Y1 : ℝ) ≤ y := by
      exact_mod_cast (le_max_left Y1 Y2).trans ((le_max_left _ 0).trans hy)
    have hlow := C_lower M hM i y
    have hc : 0 ≤ (1 - M.γ) * M.c * y := by
      rw [one_sub_gamma M hM, c]
      have := hM.cbar_nonneg; have := hM.α_pos
      positivity
    have h1 : R / (M.β * M.h) + m < y * M.lapL := by
      rw [div_lt_iff₀ hl] at hY1; nlinarith
    have h2 : R < M.β * M.h * (y * M.lapL - m) := by
      rw [div_add' _ _ _ (by positivity), div_lt_iff₀ (by positivity)] at h1; nlinarith
    unfold Gplus; nlinarith
  · have hy0 : y ≤ 0 := hy.trans (by have := le_max_right (max Y1 Y2) 0; omega)
    have hyY : (Y2 : ℝ) ≤ -y := by
      have : Y2 ≤ -y := by have := le_max_right Y1 Y2; have := le_max_left (max Y1 Y2) 0; omega
      exact_mod_cast this
    unfold Gplus
    rw [C_nonpos M hM i y hy0, one_sub_gamma M hM, c]
    rw [div_lt_iff₀ hs] at hY2
    nlinarith

theorem ystar_main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    ∃ ystar, IsYStar M ystar := by
  obtain ⟨WB, hWBm, hWB⟩ := lemma4_main M hM hA1 0 le_rfl 0 0 monotone_const
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have hall : ∀ n i x, 0 ≤ W M 0 0 n i x ∧ W M 0 0 n i x ≤ WB x := by
    intro n i x
    cases n with
    | zero =>
      have := hWB 1 le_rfl i x
      exact ⟨le_rfl, this.1.trans this.2⟩
    | succ n => exact hWB (n + 1) (by omega) i x
  have hGn : ∀ n i y, G M 0 0 (n + 1) i y = contG M (W M 0 0 n) i y := fun n i y => rfl
  have hbdd : ∀ i y, BddAbove (Set.range fun n : ℕ => G M 0 0 (n + 1) i y) := by
    intro i y
    refine ⟨M.Gplus i y + M.β * (⨆ j, M.lam j) * M.c + M.γ * WB y, ?_⟩
    rintro _ ⟨n, rfl⟩
    show G M 0 0 (n + 1) i y ≤ _
    rw [hGn]
    exact (contG_bounds M hM hA1 WB hWBm (W M 0 0 n) (hall n) i y).2
  have hlow : ∀ i y, M.Gplus i y ≤ Glin M i y := by
    intro i y
    refine (contG_ge M hM (W M 0 0 0) (fun j y => (hall 0 j y).1) i y).trans ?_
    rw [← hGn]
    exact le_ciSup (hbdd i y) 0
  have hex : ∀ i, ∃ y, IsSmallestMin (Glin M i) y := by
    intro i
    obtain ⟨Y, hY0, hY⟩ := Gplus_far M hM hA1 i (Glin M i 0)
    have hout : ∀ w, (Y ≤ w ∨ w ≤ -Y) → Glin M i 0 < Glin M i w :=
      fun w hw => (hY w hw).trans_le (hlow i w)
    obtain ⟨y0, hy0, hmin⟩ := (Finset.Icc (-Y) Y).exists_min_image (Glin M i)
      ⟨0, Finset.mem_Icc.2 ⟨by omega, hY0⟩⟩
    have h0 := hmin 0 (Finset.mem_Icc.2 ⟨by omega, hY0⟩)
    have hglob : ∀ w, Glin M i y0 ≤ Glin M i w := by
      intro w
      by_cases hw : Y ≤ w ∨ w ≤ -Y
      · exact h0.trans (hout w hw).le
      · exact hmin w (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    obtain ⟨lb, hlb, hlbmin⟩ := Int.exists_least_of_bdd
      (P := fun z => ∀ w, Glin M i z ≤ Glin M i w)
      ⟨-Y, fun z hz => by
        by_contra h
        exact absurd (hz 0) (not_le.2 (hout z (Or.inr (by omega))))⟩ ⟨y0, hglob⟩
    exact ⟨lb, hlb, fun z hz => hlbmin z hz⟩
  choose ys hys using hex
  exact ⟨ys, hys⟩


lemma K_nonneg (hM : M.Standing) : 0 ≤ M.K := mul_nonneg hM.Kbar_nonneg (lapL_pos M hM).le

lemma Wterm_bdd (Wc : I → ℤ → ℝ) (K : ℝ) (hK : 0 ≤ K) (h0 : ∀ i y, 0 ≤ contG M Wc i y) (i : I) (x : ℤ) :
    BddBelow (Set.range fun y : {y : ℤ // x ≤ y} =>
      K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M Wc i y.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  have : 0 ≤ SongZipkinFluct.Linear.delta (y.1 - x) := by
    unfold SongZipkinFluct.Linear.delta; split_ifs <;> norm_num
  exact add_nonneg (mul_nonneg hK this) (h0 i y.1)

lemma W0_all (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    ∃ V : ℤ → ℝ, Monotone V ∧ ∀ n i x, 0 ≤ W M 0 0 n i x ∧ W M 0 0 n i x ≤ V x := by
  obtain ⟨WB, hWBm, hWB⟩ := lemma4_main M hM hA1 0 le_rfl 0 0 monotone_const
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  refine ⟨WB, hWBm, fun n i x => ?_⟩
  cases n with
  | zero =>
    have := hWB 1 le_rfl i x
    exact ⟨le_rfl, this.1.trans this.2⟩
  | succ n => exact hWB (n + 1) (by omega) i x

lemma W0_mono (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (n : ℕ) (i : I) :
    Monotone (W M 0 0 n i) := by
  cases n with
  | zero => intro x y _; exact le_rfl
  | succ n =>
    obtain ⟨V, hV, hb⟩ := W0_all M hM hA1
    have h0 : ∀ i y, 0 ≤ contG M (W M 0 0 n) i y := fun i y =>
      (Gplus_nonneg M hM hA1 i y).trans (contG_ge M hM _ (fun j y => (hb n j y).1) i y)
    intro x x' hxx
    show (⨅ y : {y : ℤ // x ≤ y}, (0:ℝ) * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M 0 0 n) i y.1)
      ≤ ⨅ y : {y : ℤ // x' ≤ y}, (0:ℝ) * SongZipkinFluct.Linear.delta (y.1 - x') + contG M (W M 0 0 n) i y.1
    have : Nonempty {y : ℤ // x' ≤ y} := ⟨⟨x', le_rfl⟩⟩
    refine le_ciInf fun y => ?_
    refine (ciInf_le (Wterm_bdd M _ 0 le_rfl h0 i x) ⟨y.1, hxx.trans y.2⟩).trans ?_
    simp

lemma Wlin_props (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    ∃ V : ℤ → ℝ, Monotone V ∧ (∀ i x, 0 ≤ Wlin M i x ∧ Wlin M i x ≤ V x) ∧
      ∀ i, Monotone (Wlin M i) := by
  obtain ⟨V, hV, hb⟩ := W0_all M hM hA1
  have hbdd : ∀ i x, BddAbove (Set.range fun n => W M 0 0 n i x) :=
    fun i x => ⟨V x, by rintro _ ⟨n, rfl⟩; exact (hb n i x).2⟩
  refine ⟨V, hV, fun i x => ⟨(hb 0 i x).1.trans (le_ciSup (hbdd i x) 0),
    ciSup_le fun n => (hb n i x).2⟩, fun i x y hxy => ?_⟩
  exact ciSup_le fun n => (W0_mono M hM hA1 n i hxy).trans (le_ciSup (hbdd i y) n)

lemma Wfix_all (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    ∃ V : ℤ → ℝ, Monotone V ∧ ∀ m i x, 0 ≤ Wfix M m i x ∧ Wfix M m i x ≤ V x := by
  obtain ⟨V0, hV0, hb0, -⟩ := Wlin_props M hM hA1
  obtain ⟨WB, hWBm, hWB⟩ := lemma4_main M hM hA1 M.K (K_nonneg M hM) (Wlin M) V0 hV0 hb0
  refine ⟨fun x => max (WB x) (V0 x), fun x y h => max_le_max (hWBm h) (hV0 h), fun m i x => ?_⟩
  cases m with
  | zero => exact ⟨(hb0 i x).1, (hb0 i x).2.trans (le_max_right _ _)⟩
  | succ m =>
    have := hWB (m + 1) (by omega) i x
    exact ⟨this.1, this.2.trans (le_max_left _ _)⟩

lemma partA (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (m : ℕ) (i : I) (x a : ℤ) (ha : 0 < a) :
    -M.K ≤ Wfix M m i (x + a) - Wfix M m i x := by
  have hK := K_nonneg M hM
  cases m with
  | zero =>
    obtain ⟨-, -, -, hmono⟩ := Wlin_props M hM hA1
    have := hmono i (by omega : x ≤ x + a)
    show -M.K ≤ Wlin M i (x + a) - Wlin M i x
    linarith
  | succ k =>
    obtain ⟨V, hV, hb⟩ := Wfix_all M hM hA1
    have h0 : ∀ i y, 0 ≤ contG M (Wfix M k) i y := fun i y =>
      (Gplus_nonneg M hM hA1 i y).trans (contG_ge M hM _ (fun j y => (hb k j y).1) i y)
    have hd : ∀ z : ℤ, 0 ≤ SongZipkinFluct.Linear.delta z ∧ SongZipkinFluct.Linear.delta z ≤ 1 :=
      fun z => by unfold SongZipkinFluct.Linear.delta; split_ifs <;> norm_num
    have hne : Nonempty {y : ℤ // x + a ≤ y} := ⟨⟨x + a, le_rfl⟩⟩
    have key : Wfix M (k + 1) i x - M.K ≤ Wfix M (k + 1) i (x + a) := by
      show (⨅ y : {y : ℤ // x ≤ y}, M.K * SongZipkinFluct.Linear.delta (y.1 - x)
          + contG M (Wfix M k) i y.1) - M.K ≤
        ⨅ y : {y : ℤ // x + a ≤ y}, M.K * SongZipkinFluct.Linear.delta (y.1 - (x + a))
          + contG M (Wfix M k) i y.1
      refine le_ciInf fun y => ?_
      have h1 := ciInf_le (Wterm_bdd M _ M.K hK h0 i x) ⟨y.1, by have := y.2; omega⟩
      have h2 := mul_le_of_le_one_right hK (hd (y.1 - x)).2
      have h3 := mul_nonneg hK (hd (y.1 - (x + a))).1
      simp only at h1
      linarith
    linarith

lemma partB (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (n : ℕ) (hn : 1 ≤ n) (i : I)
    (x a : ℤ) (ha : 0 < a) :
    M.Gplus i (x + a) - M.Gplus i x - M.γ * M.K ≤ Gfix M n i (x + a) - Gfix M n i x := by
  obtain ⟨V, hV, hb⟩ := Wfix_all M hM hA1
  set Wc := Wfix M (n - 1) with hWc
  have hGf : ∀ y, Gfix M n i y = contG M Wc i y := fun y => rfl
  have hA : ∀ j z, -M.K ≤ Wc j (z + a) - Wc j z := fun j z => partA M hM hA1 (n - 1) j z a ha
  have hK := K_nonneg M hM
  have hb' := beta_pos M hM
  have hl := hM.lam_nonneg i
  have hr := rate_le M hM i
  -- the j-sums
  have hsum : ∀ z, Summable (fun j => if j = i then 0 else M.Q i j * Wc j z) := by
    intro z
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((hM.conservative i).summable.mul_right (V z))
    · split_ifs with hj
      · exact le_rfl
      · exact mul_nonneg (hM.offdiag_nonneg i j hj) (hb _ j z).1
    · split_ifs with hj
      · simp
      · exact mul_le_mul_of_nonneg_left (hb _ j z).2 (hM.offdiag_nonneg i j hj)
  have hT : (∑' j, if j = i then 0 else M.Q i j * Wc j x) - M.qrate i * M.K ≤
      ∑' j, if j = i then 0 else M.Q i j * Wc j (x + a) := by
    have hS := (hsum x).hasSum.sub ((hM.conservative i).mul_right M.K)
    rw [← hS.tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) hS.summable (hsum (x + a))
    split_ifs with hj
    · simp
    · have := mul_le_mul_of_nonneg_left (hA j x) (hM.offdiag_nonneg i j hj)
      nlinarith
  have h1 := hA i (x - 1)
  rw [show x - 1 + a = x + a - 1 by ring] at h1
  have h2 := hA i x
  rw [hGf, hGf]
  unfold contG
  rw [gamma_def M hM]
  have hmq : 0 ≤ M.μ - M.lam i - M.qrate i := by linarith
  have e1 := mul_le_mul_of_nonneg_left h1 hl
  have e2 := mul_le_mul_of_nonneg_left h2 hmq
  have : -(M.μ * M.K) ≤ M.lam i * (Wc i (x + a - 1) - Wc i (x - 1))
      + ((∑' j, if j = i then 0 else M.Q i j * Wc j (x + a))
        - (∑' j, if j = i then 0 else M.Q i j * Wc j x))
      + (M.μ - M.lam i - M.qrate i) * (Wc i (x + a) - Wc i x) := by nlinarith
  nlinarith

end SZFYP

namespace SZFScarf
open SongZipkinFluct.FixedCost

/-- the (r,S) value function -/
noncomputable def F (K : ℝ) (G : ℤ → ℝ) (r S : ℤ) (x : ℤ) : ℝ := if x ≤ r then K + G S else G x

lemma lconvex_mono {K K' : ℝ} (h : K ≤ K') {f : ℤ → ℝ} (hf : LConvex K f) : LConvex K' f :=
  fun x a b ha hb => (hf x a b ha hb).trans (by linarith)

lemma delta_eq (z : ℤ) : SongZipkinFluct.Linear.delta z = if z = 0 then 0 else 1 := rfl

variable {K : ℝ} (hK : 0 ≤ K) {G : ℤ → ℝ} (hG : LConvex K G) {r S : ℤ} (hrs : IsRSParams K G r S)
include hK hG hrs

lemma facts :
    (∀ y, G S ≤ G y) ∧ r < S ∧ K + G S < G r ∧ (∀ y, r < y → y < S → G y ≤ K + G S) ∧
      (∀ x, x ≤ r → K + G S ≤ G x) ∧ (∀ x y, S ≤ x → x ≤ y → G x ≤ G y + K) := by
  obtain ⟨⟨hSmin, -⟩, ⟨⟨hrS, hr⟩, hrmax⟩⟩ := hrs
  have h3 : ∀ y, r < y → y < S → G y ≤ K + G S := by
    intro y h1 h2; by_contra h; exact absurd (hrmax ⟨h2, not_le.1 h⟩) (not_le.2 h1)
  have h4 : ∀ x, x ≤ r → K + G S ≤ G x := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx
    · exact hr.le
    · have := hG r (S - r) (r - x) (by omega) (by omega)
      rw [show r + (S - r) = S by ring, show r - (r - x) = x by ring] at this
      have hb : (0 : ℝ) < ((r - x : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < r - x)
      have ha : (0 : ℝ) < ((S - r : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < S - r)
      by_contra hc
      have : 0 < (G r - G x) / ((r - x : ℤ) : ℝ) * ((S - r : ℤ) : ℝ) := by
        apply mul_pos _ ha; apply div_pos _ hb; linarith
      linarith
  have h5 : ∀ x y, S ≤ x → x ≤ y → G x ≤ G y + K := by
    intro x y hx hy
    rcases eq_or_lt_of_le hy with rfl | hy
    · linarith
    rcases eq_or_lt_of_le hx with rfl | hx
    · linarith [hSmin y]
    have := hG x (y - x) (x - S) (by omega) (by omega)
    rw [show x + (y - x) = y by ring, show x - (x - S) = S by ring] at this
    have hb : (0 : ℝ) < ((x - S : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < x - S)
    have ha : (0 : ℝ) < ((y - x : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < y - x)
    have : 0 ≤ (G x - G S) / ((x - S : ℤ) : ℝ) * ((y - x : ℤ) : ℝ) :=
      mul_nonneg (div_nonneg (by linarith [hSmin x]) hb.le) ha.le
    linarith
  exact ⟨hSmin, hrS, hr, h3, h4, h5⟩

lemma value_isLeast (x : ℤ) :
    IsLeast (Set.range fun y : {y : ℤ // x ≤ y} =>
        K * SongZipkinFluct.Linear.delta (y.1 - x) + G y.1)
      (K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x) + G (if x ≤ r then S else x)) := by
  obtain ⟨hSmin, hrS, hr, h3, h4, h5⟩ := facts hK hG hrs
  have hval : K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x)
      + G (if x ≤ r then S else x) = F K G r S x := by
    unfold F; split_ifs with h
    · rw [delta_eq, if_neg (by omega)]; ring
    · simp [delta_eq]
  refine ⟨⟨⟨if x ≤ r then S else x, by split_ifs <;> omega⟩, rfl⟩, ?_⟩
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  rw [hval]
  simp only [delta_eq]
  unfold F
  split_ifs with hxr hyx
  · have : y = x := by omega
    subst this; simp; exact h4 y hxr
  · linarith [hSmin y]
  · have : y = x := by omega
    subst this; simp
  · have hyx' : x < y := lt_of_le_of_ne hy (fun h => by apply ‹¬y - x = 0›; omega)
    simp only [mul_one]
    rcases le_or_gt x S with hxS | hxS
    · rcases eq_or_lt_of_le hxS with rfl | hxS
      · linarith [hSmin y]
      · linarith [h3 x (by omega) hxS, hSmin y]
    · linarith [h5 x y hxS.le hy]

lemma F_ge (z : ℤ) : G S ≤ F K G r S z := by
  obtain ⟨hSmin, -⟩ := facts hK hG hrs
  unfold F; split_ifs
  · linarith
  · exact hSmin z

lemma F_lconvex : LConvex K (F K G r S) := by
  obtain ⟨hSmin, hrS, hr, h3, h4, h5⟩ := facts hK hG hrs
  intro x a b ha hb
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  by_cases hx : x ≤ r
  · have e1 : F K G r S x = K + G S := by unfold F; rw [if_pos hx]
    have e2 : F K G r S (x - b) = K + G S := by unfold F; rw [if_pos (by omega)]
    rw [e1, e2, sub_self, zero_div, zero_mul, zero_add]
    linarith [F_ge hK hG hrs (x + a)]
  have e1 : F K G r S x = G x := by unfold F; rw [if_neg hx]
  have e3 : F K G r S (x + a) = G (x + a) := by unfold F; rw [if_neg (by omega)]
  by_cases hxb : x - b ≤ r
  · have e2 : F K G r S (x - b) = K + G S := by unfold F; rw [if_pos hxb]
    rw [e1, e2, e3]
    -- G x ≤ G (x+a) + K
    have hGx : G x ≤ G (x + a) + K := by
      rcases le_or_gt x S with hxS | hxS
      · rcases eq_or_lt_of_le hxS with rfl | hxS
        · linarith [hSmin (x + a)]
        · linarith [h3 x (by omega) hxS, hSmin (x + a)]
      · exact h5 x (x + a) hxS.le (by omega)
    by_cases hpos : G x - (K + G S) ≤ 0
    · have : (G x - (K + G S)) / (b : ℝ) * a ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hpos hbR.le) haR.le
      linarith
    · push Not at hpos
      have hxS : S < x := by
        by_contra h; push Not at h
        rcases eq_or_lt_of_le h with rfl | h
        · linarith
        · linarith [h3 x (by omega) h]
      have hc := hG x a (x - S) ha (by omega)
      rw [show x - (x - S) = S by ring] at hc
      have hd : (0 : ℝ) < ((x - S : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < x - S)
      have hbd : ((x - S : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : x - S ≤ b)
      have : (G x - (K + G S)) / (b : ℝ) ≤ (G x - G S) / ((x - S : ℤ) : ℝ) := by
        calc (G x - (K + G S)) / (b : ℝ) ≤ (G x - (K + G S)) / ((x - S : ℤ) : ℝ) :=
              div_le_div_of_nonneg_left hpos.le hd hbd
          _ ≤ (G x - G S) / ((x - S : ℤ) : ℝ) := by gcongr; linarith
      have := mul_le_mul_of_nonneg_right this haR.le
      linarith
  · have e2 : F K G r S (x - b) = G (x - b) := by unfold F; rw [if_neg hxb]
    rw [e1, e2, e3]; exact hG x a b ha hb

end SZFScarf

namespace SZFYP
open SongZipkinFluct.FixedCost SongZipkinFluct.FixedCost.Model

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

lemma lconvex_iff_mul {K : ℝ} {f : ℤ → ℝ} : LConvex K f ↔ ∀ x a b : ℤ, 0 < a → 0 < b →
    (a : ℝ) * (f x - f (x - b)) + b * f x ≤ b * f (x + a) + b * K := by
  constructor
  · intro h x a b ha hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 := mul_le_mul_of_nonneg_left (h x a b ha hb) hbR.le
    have e : (b : ℝ) * ((f x - f (x - b)) / b * a + f x) = a * (f x - f (x - b)) + b * f x := by
      field_simp
    nlinarith
  · intro h x a b ha hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 := h x a b ha hb
    have e : (f x - f (x - b)) / b * a + f x = (a * (f x - f (x - b)) + b * f x) / b := by
      field_simp
    rw [e, div_le_iff₀ hbR]; linarith

lemma Chat_cvx (hM : M.Standing) (u A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A * (M.Chat u - M.Chat (u - B)) + B * M.Chat u ≤ B * M.Chat (u + A) := by
  have g1 : ∀ t, -M.p * t ≤ M.Chat t := fun t => by
    unfold Chat; split_ifs with h
    · exact le_rfl
    · nlinarith [hM.h_pos, hM.p_pos]
  have g2 : ∀ t, M.h * t ≤ M.Chat t := Chat_ge M hM
  have h1 := mul_le_mul_of_nonneg_left (g1 (u - B)) hA
  have h2 := mul_le_mul_of_nonneg_left (g1 (u + A)) hB
  have h3 := mul_le_mul_of_nonneg_left (g2 (u - B)) hA
  have h4 := mul_le_mul_of_nonneg_left (g2 (u + A)) hB
  unfold Chat at *
  split_ifs at * <;> nlinarith

lemma C_summable (hM : M.Standing) (i : I) (y : ℤ) :
    Summable (fun d : ℕ => M.discDemandMass i d * M.Chat ((y : ℝ) - (d : ℝ))) := by
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

lemma Gplus_lconvex (hM : M.Standing) (i : I) : LConvex 0 (M.Gplus i) := by
  rw [lconvex_iff_mul]
  intro x a b ha hb
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb.le
  -- the C part
  have hC : (a : ℝ) * (M.C i x - M.C i (x - b)) + b * M.C i x ≤ b * M.C i (x + a) := by
    have hS := (((C_summable M hM i x).hasSum.mul_left ((a : ℝ) + b)).sub
      ((C_summable M hM i (x - b)).hasSum.mul_left (a : ℝ))).sub
      ((C_summable M hM i (x + a)).hasSum.mul_left (b : ℝ))
    have hle : ∑' d : ℕ, (((a : ℝ) + b) * (M.discDemandMass i d * M.Chat ((x : ℝ) - d))
        - a * (M.discDemandMass i d * M.Chat (((x - b : ℤ) : ℝ) - d))
        - b * (M.discDemandMass i d * M.Chat (((x + a : ℤ) : ℝ) - d))) ≤ 0 := by
      refine tsum_nonpos fun d => ?_
      have hc := Chat_cvx M hM ((x : ℝ) - d) a b haR hbR
      have hg := g_nonneg M hM i d
      push_cast
      rw [show (x : ℝ) - b - d = (x : ℝ) - d - b by ring, show (x : ℝ) + a - d = (x : ℝ) - d + a by ring]
      nlinarith [mul_le_mul_of_nonneg_left hc hg]
    rw [hS.tsum_eq] at hle
    unfold C; linarith
  unfold Gplus
  have hb' := beta_pos M hM
  have := mul_le_mul_of_nonneg_left hC hb'.le
  push_cast
  nlinarith

lemma contG_lconvex (hM : M.Standing) (K : ℝ) (hK : 0 ≤ K) (V : ℤ → ℝ)
    (Wc : I → ℤ → ℝ) (hW : ∀ j y, 0 ≤ Wc j y ∧ Wc j y ≤ V y) (hcv : ∀ j, LConvex K (Wc j))
    (i : I) : LConvex K (contG M Wc i) := by
  rw [lconvex_iff_mul]
  intro x a b ha hb
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb.le
  have hb' := beta_pos M hM
  have hl := hM.lam_nonneg i
  have hr := rate_le M hM i
  have hq := qrate_nonneg M hM i
  have hmq : 0 ≤ M.μ - M.lam i - M.qrate i := by linarith
  have hsum : ∀ z, Summable (fun j => if j = i then 0 else M.Q i j * Wc j z) := by
    intro z
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((hM.conservative i).summable.mul_right (V z))
    · split_ifs with hj
      · exact le_rfl
      · exact mul_nonneg (hM.offdiag_nonneg i j hj) (hW j z).1
    · split_ifs with hj
      · simp
      · exact mul_le_mul_of_nonneg_left (hW j z).2 (hM.offdiag_nonneg i j hj)
  set T := fun z => ∑' j, if j = i then 0 else M.Q i j * Wc j z with hTdef
  have hT : (a : ℝ) * (T x - T (x - b)) + b * T x ≤ b * T (x + a) + b * (M.qrate i * K) := by
    have hS := ((((hsum x).hasSum.mul_left ((a : ℝ) + b)).sub
      ((hsum (x - b)).hasSum.mul_left (a : ℝ))).sub ((hsum (x + a)).hasSum.mul_left (b : ℝ)))
    have hQ := (hM.conservative i).mul_right ((b : ℝ) * K)
    have hle := hasSum_le ?_ hS hQ
    · simp only [hTdef]; linarith
    intro j
    split_ifs with hj
    · simp
    · have := (lconvex_iff_mul.1 (hcv j)) x a b ha hb
      have hQ0 := hM.offdiag_nonneg i j hj
      nlinarith [mul_le_mul_of_nonneg_left this hQ0]
  have h1 := (lconvex_iff_mul.1 (hcv i)) (x - 1) a b ha hb
  rw [show x - 1 - b = x - b - 1 by ring, show x - 1 + a = x + a - 1 by ring] at h1
  have h2 := (lconvex_iff_mul.1 (hcv i)) x a b ha hb
  have h3 := (lconvex_iff_mul.1 (Gplus_lconvex M hM i)) x a b ha hb
  have hγ : M.β * M.μ ≤ 1 := by
    have := gamma_lt M hM; rw [gamma_def M hM] at this; linarith
  have e1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hb'.le hl)
  have e2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hb'.le hmq)
  have e3 := mul_le_mul_of_nonneg_left hT hb'.le
  have e4 : M.β * M.μ * (b * K) ≤ b * K := by
    have := mul_nonneg hbR hK; nlinarith
  have hTx : (∑' j, if j = i then 0 else M.Q i j * Wc j x) = T x := rfl
  have hTxb : (∑' j, if j = i then 0 else M.Q i j * Wc j (x - b)) = T (x - b) := rfl
  have hTxa : (∑' j, if j = i then 0 else M.Q i j * Wc j (x + a)) = T (x + a) := rfl
  unfold contG
  rw [hTx, hTxb, hTxa, show x - b - 1 = x - b - 1 from rfl]
  simp only [mul_zero, add_zero] at h3
  nlinarith

lemma contG_mono (hM : M.Standing) (V : ℤ → ℝ) (Wc Wc' : I → ℤ → ℝ)
    (hW : ∀ j y, 0 ≤ Wc j y ∧ Wc j y ≤ V y) (hW' : ∀ j y, 0 ≤ Wc' j y ∧ Wc' j y ≤ V y)
    (hle : ∀ j y, Wc j y ≤ Wc' j y) (i : I) (y : ℤ) : contG M Wc i y ≤ contG M Wc' i y := by
  have hb' := beta_pos M hM
  have hl := hM.lam_nonneg i
  have hr := rate_le M hM i
  have hmq : 0 ≤ M.μ - M.lam i - M.qrate i := by linarith
  have hsum : ∀ (U : I → ℤ → ℝ), (∀ j y, 0 ≤ U j y ∧ U j y ≤ V y) →
      Summable (fun j => if j = i then 0 else M.Q i j * U j y) := by
    intro U hU
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((hM.conservative i).summable.mul_right (V y))
    · split_ifs with hj
      · exact le_rfl
      · exact mul_nonneg (hM.offdiag_nonneg i j hj) (hU j y).1
    · split_ifs with hj
      · simp
      · exact mul_le_mul_of_nonneg_left (hU j y).2 (hM.offdiag_nonneg i j hj)
  have hT : (∑' j, if j = i then 0 else M.Q i j * Wc j y) ≤
      ∑' j, if j = i then 0 else M.Q i j * Wc' j y := by
    refine Summable.tsum_le_tsum (fun j => ?_) (hsum Wc hW) (hsum Wc' hW')
    split_ifs with hj
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hle j y) (hM.offdiag_nonneg i j hj)
  have e1 := mul_le_mul_of_nonneg_left (hle i (y - 1)) hl
  have e2 := mul_le_mul_of_nonneg_left (hle i y) hmq
  unfold contG
  have : M.lam i * Wc i (y - 1) + (∑' j, if j = i then 0 else M.Q i j * Wc j y)
      + (M.μ - M.lam i - M.qrate i) * Wc i y ≤ M.lam i * Wc' i (y - 1)
      + (∑' j, if j = i then 0 else M.Q i j * Wc' j y) + (M.μ - M.lam i - M.qrate i) * Wc' i y := by
    linarith
  nlinarith

/-- existence of (r,S) parameters for a K-convex function coercive at both ends -/
lemma rs_exist (K : ℝ) (hK : 0 ≤ K) (G : ℤ → ℝ)
    (hcoer : ∀ R, ∃ Y : ℤ, 0 ≤ Y ∧ ∀ y, (Y ≤ y ∨ y ≤ -Y) → R < G y) :
    ∃ r S, IsRSParams K G r S := by
  obtain ⟨Y, hY0, hY⟩ := hcoer (G 0)
  obtain ⟨y0, hy0, hmin⟩ := (Finset.Icc (-Y) Y).exists_min_image G
    ⟨0, Finset.mem_Icc.2 ⟨by omega, hY0⟩⟩
  have h0 := hmin 0 (Finset.mem_Icc.2 ⟨by omega, hY0⟩)
  have hglob : ∀ w, G y0 ≤ G w := by
    intro w
    by_cases hw : Y ≤ w ∨ w ≤ -Y
    · exact h0.trans (hY w hw).le
    · exact hmin w (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨S, hS, hSmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∀ w, G z ≤ G w)
    ⟨-Y, fun z hz => by
      by_contra h
      exact absurd (hz 0) (not_le.2 (hY z (Or.inr (by omega))))⟩ ⟨y0, hglob⟩
  obtain ⟨Y2, hY20, hY2⟩ := hcoer (K + G S)
  obtain ⟨r, hr, hrmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => z < S ∧ K + G S < G z)
    ⟨S, fun z hz => hz.1.le⟩
    ⟨min (-Y2) (S - 1), by omega, hY2 _ (Or.inr (min_le_left _ _))⟩
  exact ⟨r, S, ⟨hS, fun z hz => hSmin z hz⟩, ⟨hr, fun z hz => hrmax z hz⟩⟩

lemma W_succ_eq (K : ℝ) (W₀ : I → ℤ → ℝ) (n : ℕ) (i : I) (x : ℤ) :
    W M K W₀ (n + 1) i x = sInf (Set.range fun y : {y : ℤ // x ≤ y} =>
      K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M K W₀ n) i y.1) := rfl

lemma Wlin_lconvex (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) :
    LConvex 0 (Wlin M i) := by
  obtain ⟨V, hV, hb⟩ := W0_all M hM hA1
  have hcv : ∀ n j, LConvex 0 (W M 0 0 n j) := by
    intro n
    induction n with
    | zero => intro j x a b _ _; simp [W]
    | succ n ih =>
      intro j
      have hG := contG_lconvex M hM 0 le_rfl V (W M 0 0 n) (hb n) ih j
      have hco : ∀ R, ∃ Y : ℤ, 0 ≤ Y ∧ ∀ y, (Y ≤ y ∨ y ≤ -Y) → R < contG M (W M 0 0 n) j y := by
        intro R
        obtain ⟨Y, hY0, hY⟩ := Gplus_far M hM hA1 j R
        exact ⟨Y, hY0, fun y hy => (hY y hy).trans_le
          (contG_ge M hM _ (fun j y => (hb n j y).1) j y)⟩
      obtain ⟨r, S, hrs⟩ := rs_exist 0 le_rfl _ hco
      have heq : W M 0 0 (n + 1) j = SZFScarf.F 0 (contG M (W M 0 0 n) j) r S := by
        funext x
        rw [W_succ_eq, (SZFScarf.value_isLeast le_rfl hG hrs x).csInf_eq]
        unfold SZFScarf.F
        split_ifs with h
        · rw [SZFScarf.delta_eq, if_neg (by have := hrs.2.1.1; omega)]; ring
        · simp [SZFScarf.delta_eq]
      rw [heq]; exact SZFScarf.F_lconvex le_rfl hG hrs
  have hbdd : ∀ x, BddAbove (Set.range fun n => W M 0 0 n i x) :=
    fun x => ⟨V x, by rintro _ ⟨n, rfl⟩; exact (hb n i x).2⟩
  rw [lconvex_iff_mul]
  intro x a b ha hb'
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb'.le
  have key : ((a : ℝ) + b) * Wlin M i x ≤ a * Wlin M i (x - b) + b * Wlin M i (x + a) := by
    have hab : (0 : ℝ) < a + b := by
      have : (0:ℝ) < b := by exact_mod_cast hb'
      linarith
    rw [← le_div_iff₀' hab]
    refine ciSup_le fun n => ?_
    rw [le_div_iff₀' hab]
    have := (lconvex_iff_mul.1 (hcv n i)) x a b ha hb'
    have h1 := mul_le_mul_of_nonneg_left (le_ciSup (hbdd (x - b)) n) haR
    have h2 := mul_le_mul_of_nonneg_left (le_ciSup (hbdd (x + a)) n) hbR
    simp only [mul_zero, add_zero] at this
    unfold Wlin
    nlinarith
  simp only [mul_zero, add_zero]
  linarith


lemma step_eq (K : ℝ) (hK : 0 ≤ K) (Wc : I → ℤ → ℝ) (j : I) (r S : ℤ)
    (hG : LConvex K (contG M Wc j)) (hrs : IsRSParams K (contG M Wc j) r S) (x : ℤ) :
    sInf (Set.range fun y : {y : ℤ // x ≤ y} =>
      K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M Wc j y.1) =
      K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x)
        + contG M Wc j (if x ≤ r then S else x) :=
  (SZFScarf.value_isLeast hK hG hrs x).csInf_eq

lemma step_F (K : ℝ) (hK : 0 ≤ K) (Wc : I → ℤ → ℝ) (j : I) (r S : ℤ)
    (hG : LConvex K (contG M Wc j)) (hrs : IsRSParams K (contG M Wc j) r S) (x : ℤ) :
    sInf (Set.range fun y : {y : ℤ // x ≤ y} =>
      K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M Wc j y.1) =
      SZFScarf.F K (contG M Wc j) r S x := by
  rw [step_eq M K hK Wc j r S hG hrs x]
  unfold SZFScarf.F
  split_ifs with h
  · rw [SZFScarf.delta_eq, if_neg (by have := hrs.2.1.1; omega)]; ring
  · simp [SZFScarf.delta_eq]

lemma coer_of_ge (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (Wc : I → ℤ → ℝ)
    (hW : ∀ j y, 0 ≤ Wc j y) (j : I) :
    ∀ R, ∃ Y : ℤ, 0 ≤ Y ∧ ∀ y, (Y ≤ y ∨ y ≤ -Y) → R < contG M Wc j y := by
  intro R
  obtain ⟨Y, hY0, hY⟩ := Gplus_far M hM hA1 j R
  exact ⟨Y, hY0, fun y hy => (hY y hy).trans_le (contG_ge M hM _ hW j y)⟩

theorem theorem3_main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) (n : ℕ)
    (hn : 1 ≤ n) :
    (LConvex M.K (Gfix M n i) ∧ Tendsto (Gfix M n i) atTop atTop ∧
        Tendsto (Gfix M n i) atBot atTop) ∧
      ((∃ r S : ℤ, IsRSParams M.K (Gfix M n i) r S) ∧
        ∀ r S : ℤ, IsRSParams M.K (Gfix M n i) r S → ∀ x : ℤ,
          Wfix M n i x = M.K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x)
            + Gfix M n i (if x ≤ r then S else x)) ∧
      (LConvex M.K (Wfix M n i) ∧ Tendsto (Wfix M n i) atTop atTop) ∧
      (∀ x : ℤ, Wfix M (n - 1) i x ≤ Wfix M n i x ∧ 0 ≤ Wfix M (n - 1) i x) ∧
      (∀ y : ℤ, Gfix M n i y ≤ Gfix M (n + 1) i y ∧ 0 ≤ Gfix M n i y) := by
  have hK := K_nonneg M hM
  obtain ⟨V, hV, hb⟩ := Wfix_all M hM hA1
  have hb0 : ∀ m j y, 0 ≤ Wfix M m j y := fun m j y => (hb m j y).1
  -- convexity of all iterates
  have hcv : ∀ m j, LConvex M.K (Wfix M m j) := by
    intro m
    induction m with
    | zero => intro j; exact SZFScarf.lconvex_mono hK (Wlin_lconvex M hM hA1 j)
    | succ m ih =>
      intro j
      have hG := contG_lconvex M hM M.K hK V (Wfix M m) (hb m) ih j
      obtain ⟨r, S, hrs⟩ := rs_exist M.K hK _ (coer_of_ge M hM hA1 _ (hb0 m) j)
      have heq : Wfix M (m + 1) j = SZFScarf.F M.K (contG M (Wfix M m) j) r S := by
        funext x
        exact step_F M M.K hK (Wfix M m) j r S hG hrs x
      rw [heq]; exact SZFScarf.F_lconvex hK hG hrs
  -- monotonicity in m
  have hmono : ∀ m j x, Wfix M m j x ≤ Wfix M (m + 1) j x := by
    intro m
    induction m with
    | zero =>
      intro j x
      obtain ⟨V0, hV0, hb0'⟩ := W0_all M hM hA1
      obtain ⟨V1, hV1, hb1, -⟩ := Wlin_props M hM hA1
      have hbdd : BddAbove (Set.range fun n => W M 0 0 n j x) :=
        ⟨V0 x, by rintro _ ⟨n, rfl⟩; exact (hb0' n j x).2⟩
      show Wlin M j x ≤ W M M.K (Wlin M) (0 + 1) j x
      refine ciSup_le fun k => ?_
      cases k with
      | zero => exact hb0 1 j x
      | succ k =>
        rw [W_succ_eq, W_succ_eq]
        have hne : (Set.range fun y : {y : ℤ // x ≤ y} =>
            M.K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M M.K (Wlin M) 0) j y.1).Nonempty :=
          ⟨_, ⟨⟨x, le_rfl⟩, rfl⟩⟩
        refine le_csInf hne ?_
        rintro _ ⟨y, rfl⟩
        have hbd : BddBelow (Set.range fun y : {y : ℤ // x ≤ y} =>
            (0:ℝ) * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (W M 0 0 k) j y.1) :=
          Wterm_bdd M _ 0 le_rfl (fun i y => (Gplus_nonneg M hM hA1 i y).trans
            (contG_ge M hM _ (fun j y => (hb0' k j y).1) i y)) j x
        refine (csInf_le hbd ⟨y, rfl⟩).trans ?_
        simp only [zero_mul, zero_add]
        have hVm : ∀ z, V0 z ≤ max (V0 z) (V1 z) := fun z => le_max_left _ _
        have h1 := contG_mono M hM (fun z => max (V0 z) (V1 z)) (W M 0 0 k) (Wlin M)
          (fun j z => ⟨(hb0' k j z).1, (hb0' k j z).2.trans (le_max_left _ _)⟩)
          (fun j z => ⟨(hb1 j z).1, (hb1 j z).2.trans (le_max_right _ _)⟩)
          (fun j z => le_ciSup (⟨V0 z, by rintro _ ⟨n, rfl⟩; exact (hb0' n j z).2⟩ :
            BddAbove (Set.range fun n => W M 0 0 n j z)) k) j y
        have hd : 0 ≤ M.K * SongZipkinFluct.Linear.delta (y.1 - x) := by
          refine mul_nonneg hK ?_
          unfold SongZipkinFluct.Linear.delta; split_ifs <;> norm_num
        exact h1.trans (le_add_of_nonneg_left hd)
    | succ m ih =>
      intro j x
      show W M M.K (Wlin M) (m + 1) j x ≤ W M M.K (Wlin M) (m + 1 + 1) j x
      rw [W_succ_eq, W_succ_eq]
      refine le_csInf ⟨_, ⟨⟨x, le_rfl⟩, rfl⟩⟩ ?_
      rintro _ ⟨y, rfl⟩
      have hbd := Wterm_bdd M (Wfix M m) M.K hK (fun i y => (Gplus_nonneg M hM hA1 i y).trans
        (contG_ge M hM _ (hb0 m) i y)) j x
      refine (csInf_le hbd ⟨y, rfl⟩).trans ?_
      have := contG_mono M hM V (Wfix M m) (Wfix M (m + 1)) (hb m) (hb (m + 1)) ih j y
      show M.K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (Wfix M m) j y.1 ≤
        M.K * SongZipkinFluct.Linear.delta (y.1 - x) + contG M (Wfix M (m + 1)) j y.1
      linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hGf : ∀ y, Gfix M (k + 1) i y = contG M (Wfix M k) i y := fun y => rfl
  have hGf' : Gfix M (k + 1) i = contG M (Wfix M k) i := rfl
  have hG := contG_lconvex M hM M.K hK V (Wfix M k) (hb k) (hcv k) i
  have hco := coer_of_ge M hM hA1 _ (hb0 k) i
  have hGplus : ∀ y, M.Gplus i y ≤ Gfix M (k + 1) i y := fun y => contG_ge M hM _ (hb0 k) i y
  refine ⟨⟨hGf' ▸ hG, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨hcv (k + 1) i, ?_⟩, ?_, ?_⟩
  · refine tendsto_atTop.2 fun R => ?_
    obtain ⟨Y, -, hY⟩ := hco R
    exact eventually_atTop.2 ⟨Y, fun y hy => (hY y (Or.inl hy)).le⟩
  · refine tendsto_atTop.2 fun R => ?_
    obtain ⟨Y, -, hY⟩ := hco R
    exact eventually_atBot.2 ⟨-Y, fun y hy => (hY y (Or.inr hy)).le⟩
  · rw [hGf']; exact rs_exist M.K hK _ hco
  · intro r S hrs x
    rw [hGf'] at hrs ⊢
    exact step_eq M M.K hK (Wfix M k) i r S hG hrs x
  · refine tendsto_atTop.2 fun R => ?_
    obtain ⟨Y, -, hY⟩ := hco R
    obtain ⟨r, S, hrs⟩ := rs_exist M.K hK _ hco
    refine eventually_atTop.2 ⟨Y, fun x hx => ?_⟩
    have e : Wfix M (k + 1) i x = _ := step_eq M M.K hK (Wfix M k) i r S hG hrs x
    rw [e]
    have hd : 0 ≤ M.K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x) := by
      refine mul_nonneg hK ?_
      unfold SongZipkinFluct.Linear.delta; split_ifs <;> norm_num
    have hp : Y ≤ (if x ≤ r then S else x) := by
      split_ifs with h
      · have := hrs.2.1.1; omega
      · exact hx
    have := hY _ (Or.inl hp)
    linarith
  · intro x
    exact ⟨hmono k i x, hb0 k i x⟩
  · intro y
    refine ⟨?_, (Gplus_nonneg M hM hA1 i y).trans (hGplus y)⟩
    show contG M (Wfix M k) i y ≤ contG M (Wfix M (k + 1)) i y
    exact contG_mono M hM V _ _ (hb k) (hb (k + 1)) (hmono k) i y


lemma lconvex_sup {K : ℝ} (f : ℕ → ℤ → ℝ) (hf : ∀ n, LConvex K (f n))
    (hbdd : ∀ x, BddAbove (Set.range fun n => f n x)) : LConvex K (fun x => ⨆ n, f n x) := by
  rw [lconvex_iff_mul]
  intro x a b ha hb'
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb'
  have hab : (0 : ℝ) < a + b := by linarith
  have key : ((a : ℝ) + b) * (⨆ n, f n x) ≤ a * (⨆ n, f n (x - b)) + b * (⨆ n, f n (x + a)) + b * K := by
    rw [← le_div_iff₀' hab]
    refine ciSup_le fun n => ?_
    rw [le_div_iff₀' hab]
    have := (lconvex_iff_mul.1 (hf n)) x a b ha hb'
    have h1 := mul_le_mul_of_nonneg_left (le_ciSup (hbdd (x - b)) n) haR
    have h2 := mul_le_mul_of_nonneg_left (le_ciSup (hbdd (x + a)) n) hbR.le
    nlinarith
  show (a : ℝ) * ((⨆ n, f n x) - ⨆ n, f n (x - b)) + b * (⨆ n, f n x)
    ≤ b * (⨆ n, f n (x + a)) + b * K
  linarith

theorem theorem5ab_main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (i : I) :
    ((∀ x : ℤ, Tendsto (fun n => Wfix M n i x) atTop (𝓝 (WinfK M i x))) ∧
        LConvex M.K (WinfK M i) ∧ Tendsto (WinfK M i) atTop atTop) ∧
      ((∀ y : ℤ, Tendsto (fun n => Gfix M n i y) atTop (𝓝 (GinfK M i y))) ∧
        LConvex M.K (GinfK M i) ∧ Tendsto (GinfK M i) atTop atTop ∧
        Tendsto (GinfK M i) atBot atTop) := by
  have hK := K_nonneg M hM
  obtain ⟨V, hV, hb⟩ := Wfix_all M hM hA1
  have t3 := fun n (hn : 1 ≤ n) => theorem3_main M hM hA1 i n hn
  have hWm : ∀ x, Monotone (fun n => Wfix M n i x) := fun x =>
    monotone_nat_of_le_succ fun m => ((t3 (m + 1) (by omega)).2.2.2.1 x).1
  have hWb : ∀ x, BddAbove (Set.range fun n => Wfix M n i x) :=
    fun x => ⟨V x, by rintro _ ⟨n, rfl⟩; exact (hb n i x).2⟩
  have hGm : ∀ y, Monotone (fun n => Gfix M (n + 1) i y) := fun y =>
    monotone_nat_of_le_succ fun m => ((t3 (m + 1) (by omega)).2.2.2.2 y).1
  have hGb : ∀ y, BddAbove (Set.range fun n => Gfix M (n + 1) i y) := fun y =>
    ⟨M.Gplus i y + M.β * (⨆ j, M.lam j) * M.c + M.γ * V y, by
      rintro _ ⟨n, rfl⟩
      exact (contG_bounds M hM hA1 V hV (Wfix M n) (hb n) i y).2⟩
  have hWcv : ∀ n, LConvex M.K (Wfix M n i) := by
    intro n
    cases n with
    | zero => exact SZFScarf.lconvex_mono hK (Wlin_lconvex M hM hA1 i)
    | succ n => exact (t3 (n + 1) (by omega)).2.2.1.1
  refine ⟨⟨fun x => tendsto_atTop_ciSup (hWm x) (hWb x),
    lconvex_sup (fun n => Wfix M n i) hWcv hWb, ?_⟩,
    ⟨fun y => ?_, lconvex_sup (fun n => Gfix M (n + 1) i) (fun n => (t3 (n + 1) (by omega)).1.1) hGb,
      ?_, ?_⟩⟩
  · exact tendsto_atTop_mono (fun x => le_ciSup (hWb x) 1) (t3 1 le_rfl).2.2.1.2
  · rw [← tendsto_add_atTop_iff_nat 1]
    exact tendsto_atTop_ciSup (hGm y) (hGb y)
  · exact tendsto_atTop_mono (fun y => le_ciSup (hGb y) 0) (t3 1 le_rfl).1.2.1
  · exact tendsto_atTop_mono (fun y => le_ciSup (hGb y) 0) (t3 1 le_rfl).1.2.2


theorem theorem5d_main (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    (∀ (i : I) (x : ℤ), IsLeast
        (Set.range fun y : {y : ℤ // x ≤ y} => M.K * SongZipkinFluct.Linear.delta (y.1 - x) + GinfK M i y.1)
        (WinfK M i x)) ∧
      ∀ (i : I) (y : ℤ), GinfK M i y = contG M (WinfK M) i y := by
  have hK := K_nonneg M hM
  obtain ⟨V, hV, hb⟩ := Wfix_all M hM hA1
  have hb0 : ∀ m j y, 0 ≤ Wfix M m j y := fun m j y => (hb m j y).1
  have t3 := fun i n (hn : 1 ≤ n) => theorem3_main M hM hA1 i n hn
  have t5 := fun i => theorem5ab_main M hM hA1 i
  have hWb : ∀ i x, BddAbove (Set.range fun n => Wfix M n i x) :=
    fun i x => ⟨V x, by rintro _ ⟨n, rfl⟩; exact (hb n i x).2⟩
  have hGb : ∀ i y, BddAbove (Set.range fun n => Gfix M (n + 1) i y) := fun i y =>
    ⟨M.Gplus i y + M.β * (⨆ j, M.lam j) * M.c + M.γ * V y, by
      rintro _ ⟨n, rfl⟩
      exact (contG_bounds M hM hA1 V hV (Wfix M n) (hb n) i y).2⟩
  have hGm : ∀ i y, Monotone (fun n => Gfix M (n + 1) i y) := fun i y =>
    monotone_nat_of_le_succ fun m => ((t3 i (m + 1) (by omega)).2.2.2.2 y).1
  have hGt : ∀ i y, Tendsto (fun n => Gfix M (n + 1) i y) atTop (𝓝 (GinfK M i y)) :=
    fun i y => tendsto_atTop_ciSup (hGm i y) (hGb i y)
  have hWinf_b : ∀ j z, 0 ≤ WinfK M j z ∧ WinfK M j z ≤ V z := fun j z =>
    ⟨(hb0 0 j z).trans (le_ciSup (hWb j z) 0), ciSup_le fun n => (hb n j z).2⟩
  refine ⟨fun i x => ?_, fun i y => ?_⟩
  · -- lower bound
    have hlow : ∀ y : {y : ℤ // x ≤ y},
        WinfK M i x ≤ M.K * SongZipkinFluct.Linear.delta (y.1 - x) + GinfK M i y.1 := by
      intro y
      refine ciSup_le fun n => ?_
      have h1 : Wfix M n i x ≤ Wfix M (n + 1) i x := ((t3 i (n + 1) (by omega)).2.2.2.1 x).1
      have hbd := Wterm_bdd M (Wfix M n) M.K hK (fun i y => (Gplus_nonneg M hM hA1 i y).trans
        (contG_ge M hM _ (hb0 n) i y)) i x
      have h2 : Wfix M (n + 1) i x ≤ M.K * SongZipkinFluct.Linear.delta (y.1 - x)
          + contG M (Wfix M n) i y.1 := by
        show W M M.K (Wlin M) (n + 1) i x ≤ _
        rw [W_succ_eq]; exact csInf_le hbd ⟨y, rfl⟩
      have h3 : contG M (Wfix M n) i y.1 ≤ GinfK M i y.1 := le_ciSup (hGb i y.1) n
      linarith
    -- uniform bound on minimizers
    obtain ⟨Y, hY⟩ := eventually_atTop.1 ((t3 i 1 le_rfl).1.2.1.eventually_gt_atTop (GinfK M i 0))
    set X := max x Y
    obtain ⟨ys, hys, hmin⟩ := (Finset.Icc x X).exists_min_image
      (fun y => M.K * SongZipkinFluct.Linear.delta (y - x) + GinfK M i y)
      ⟨x, Finset.mem_Icc.2 ⟨le_rfl, le_max_left _ _⟩⟩
    have hxys : x ≤ ys := (Finset.mem_Icc.1 hys).1
    have hge : M.K * SongZipkinFluct.Linear.delta (ys - x) + GinfK M i ys ≤ WinfK M i x := by
      by_contra hcon
      push Not at hcon
      have hev : ∀ᶠ n in atTop, ∀ y ∈ Finset.Icc x X,
          WinfK M i x < M.K * SongZipkinFluct.Linear.delta (y - x) + Gfix M (n + 1) i y := by
        rw [Filter.eventually_all_finset]
        intro y hy
        have hlt : WinfK M i x < M.K * SongZipkinFluct.Linear.delta (y - x) + GinfK M i y :=
          hcon.trans_le (hmin y hy)
        exact (tendsto_const_nhds.add (hGt i y)).eventually (lt_mem_nhds hlt)
      obtain ⟨n, hn⟩ := hev.exists
      obtain ⟨r, S, hrs⟩ := (t3 i (n + 1) (by omega)).2.1.1
      have heq := (t3 i (n + 1) (by omega)).2.1.2 r S hrs x
      have hSY : S < Y := by
        by_contra hSY; push Not at hSY
        have a1 := hY S hSY
        have a2 : Gfix M 1 i S ≤ Gfix M (n + 1) i S := hGm i S (Nat.zero_le n)
        have a3 : Gfix M (n + 1) i S ≤ Gfix M (n + 1) i 0 := hrs.1.1 0
        have a4 : Gfix M (n + 1) i 0 ≤ GinfK M i 0 := le_ciSup (hGb i 0) n
        linarith
      have hpol : (if x ≤ r then S else x) ∈ Finset.Icc x X := by
        refine Finset.mem_Icc.2 ⟨?_, ?_⟩
        · split_ifs with h
          · have := hrs.2.1.1; omega
          · exact le_rfl
        · split_ifs with h
          · exact (le_max_right _ _).trans' hSY.le
          · exact le_max_left _ _
      have h1 := hn _ hpol
      rw [← heq] at h1
      have h2 : Wfix M (n + 1) i x ≤ WinfK M i x := le_ciSup (hWb i x) (n + 1)
      linarith
    exact ⟨⟨⟨ys, hxys⟩, le_antisymm hge (hlow ⟨ys, hxys⟩)⟩, by rintro _ ⟨y, rfl⟩; exact hlow y⟩
  · -- G_∞ = contG W_∞
    have hWt : ∀ j z, Tendsto (fun n => Wfix M n j z) atTop (𝓝 (WinfK M j z)) :=
      fun j z => (t5 j).1.1 z
    have hT : Tendsto (fun n => ∑' j, if j = i then 0 else M.Q i j * Wfix M n j y) atTop
        (𝓝 (∑' j, if j = i then 0 else M.Q i j * WinfK M j y)) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun j => (if j = i then 0 else M.Q i j) * V y)
        ((hM.conservative i).summable.mul_right (V y)) (fun j => ?_) ?_
      · split_ifs
        · exact tendsto_const_nhds
        · exact (hWt j y).const_mul _
      · refine Eventually.of_forall fun n j => ?_
        split_ifs with hj
        · simp
        · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hM.offdiag_nonneg i j hj),
            abs_of_nonneg (hb0 n j y)]
          exact mul_le_mul_of_nonneg_left (hb n j y).2 (hM.offdiag_nonneg i j hj)
    have hlim : Tendsto (fun n => Gfix M (n + 1) i y) atTop (𝓝 (contG M (WinfK M) i y)) := by
      have : (fun n => Gfix M (n + 1) i y) = fun n => contG M (Wfix M n) i y := rfl
      rw [this]
      unfold contG
      refine tendsto_const_nhds.add (((((hWt i (y - 1)).const_mul _).add hT).add
        ((hWt i y).const_mul _)).const_mul _)
    exact tendsto_nhds_unique (hGt i y) hlim

end SZFYP

open SongZipkinFluct.FixedCost Filter Topology in
theorem solution {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    (∀ (i : I) (x : ℤ), IsLeast
        (Set.range fun y : {y : ℤ // x ≤ y} => M.K * SongZipkinFluct.Linear.delta (y.1 - x) + GinfK M i y.1)
        (WinfK M i x)) ∧
      ∀ (i : I) (y : ℤ), GinfK M i y = contG M (WinfK M) i y :=
  SZFYP.theorem5d_main M hM hA1
