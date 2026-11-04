-- Prove2me | solution 1 for PerishBaseStock.Outdating.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:48:49.089964+00:00
-- url     : https://prove2.me/submissions/7b4ea706-0676-418a-b7f8-6088dda6ff13

import Theorems.Thm_PerishBaseStock_Outdating_eq_24
import Theorems.Thm_PerishBaseStock_Lifetime_eq_21_gap_bound

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

namespace PBS4R
open PerishBaseStock

/-- Embedding of an `ℝ≥0`-valued state into the real-valued state space. -/
def emb {m : ℕ} (x : Population.State m) : Lifetime.State m := fun j => ((x j : ℝ≥0) : ℝ)

theorem topLevel_emb {m : ℕ} (x : Population.State m) :
    Lifetime.topLevel (emb x) = ((Population.topLevel x : ℝ≥0) : ℝ) := by
  unfold Lifetime.topLevel Population.topLevel emb
  split_ifs <;> simp

theorem onHand_eq {m : ℕ} (x : Population.State m) :
    Outdating.onHand x = Population.topLevel x := by
  unfold Outdating.onHand Population.topLevel
  split_ifs <;> first | rfl | omega

theorem coe_tsub (a b : ℝ≥0) : ((a - b : ℝ≥0) : ℝ) = max ((a : ℝ) - b) 0 := NNReal.coe_sub_def

theorem firstLevel_emb {m : ℕ} (x : Population.State m) (q : ℝ≥0) :
    Lifetime.firstLevel (emb x) q = ((Population.level x q 1 : ℝ≥0) : ℝ) := by
  unfold Lifetime.firstLevel Population.level Lifetime.orderUpTo
  rw [topLevel_emb]
  split_ifs with h1 h2 h3 <;> first | omega | simp [emb]

theorem outdate_emb {m : ℕ} (x : Population.State m) (q d : ℝ≥0) :
    Lifetime.outdate (emb x) q d = ((Population.outdate x q d : ℝ≥0) : ℝ) := by
  unfold Lifetime.outdate Population.outdate
  rw [firstLevel_emb, coe_tsub]

theorem step_emb {m : ℕ} (x : Population.State m) (q d : ℝ≥0) :
    Lifetime.step (emb x) q d = emb (Population.next x q d) := by
  funext j
  have hlev : Lifetime.levelAbove (emb x) q j = ((Population.level x q (j.val + 2) : ℝ≥0) : ℝ) := by
    unfold Lifetime.levelAbove Population.level Lifetime.orderUpTo
    rw [topLevel_emb]
    have hj := j.isLt
    split_ifs with h1 h2 h3 h4 <;> first | omega | simp [emb]
  unfold Lifetime.step
  rw [hlev, outdate_emb]
  simp only [emb, Population.next]
  rw [coe_tsub, coe_tsub]
  set a : ℝ := ((Population.level x q (j.val + 2) : ℝ≥0) : ℝ)
  set o : ℝ := ((Population.outdate x q d : ℝ≥0) : ℝ)
  have ho : 0 ≤ o := NNReal.coe_nonneg _
  have hd : 0 ≤ ((d : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  rcases le_total (a - d) 0 with h | h
  · rw [max_eq_right h]; simp only [zero_sub]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h]

/-- A real-state policy `ψ` that agrees with `π` on embedded states. -/
def Agrees {m : ℕ} (ψ : Lifetime.Policy m) (π : Population.Policy m) : Prop :=
  ∀ t x, ψ.φ t (emb x) = π.φ t x

theorem run_emb {m : ℕ} (ψ : Lifetime.Policy m) (π : Population.Policy m) (h : Agrees ψ π)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.run ψ d t = emb (Population.run π d t) := by
  induction t with
  | zero =>
    funext j; simp [Lifetime.run, Lifetime.runFrom, Lifetime.emptyState, Population.run,
      Population.emptyState, emb]
  | succ t ih =>
    have : Lifetime.run ψ d (t + 1) =
        Lifetime.step (Lifetime.run ψ d t) (ψ.φ t (Lifetime.run ψ d t)) (d t) := rfl
    rw [this, ih, h, step_emb]
    rfl

/-- The `Lifetime` parameters corresponding to `(c, θ)`. -/
abbrev toL (c : Outdating.Params) (θ : ℝ≥0) : Lifetime.Params where
  m := c.m
  one_le_m := c.one_le_m
  h := c.h
  p := c.p
  θ := (θ : ℝ)
  h_pos := c.h_pos
  p_pos := c.p_pos
  θ_nonneg := θ.2

theorem upTo_eq {m : ℕ} (ψ : Lifetime.Policy m) (π : Population.Policy m) (h : Agrees ψ π)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.upTo ψ d t = ((Outdating.orderUpTo π d t : ℝ≥0) : ℝ) := by
  have hrun := run_emb ψ π h d t
  have e1 : Lifetime.upTo ψ d t =
      Lifetime.orderUpTo (Lifetime.run ψ d t) (ψ.φ t (Lifetime.run ψ d t)) := rfl
  rw [e1, hrun, h]
  unfold Outdating.orderUpTo Lifetime.orderUpTo
  rw [topLevel_emb, onHand_eq]; push_cast; ring

theorem outdated_eq {m : ℕ} (ψ : Lifetime.Policy m) (π : Population.Policy m) (h : Agrees ψ π)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.outdated ψ d t = ((Outdating.outdatedAt π d t : ℝ≥0) : ℝ) := by
  have hrun := run_emb ψ π h d t
  have e1 : Lifetime.outdated ψ d t =
      Lifetime.outdate (Lifetime.run ψ d t) (ψ.φ t (Lifetime.run ψ d t)) (d t) := rfl
  rw [e1, hrun, h, outdate_emb]
  unfold Outdating.outdatedAt Outdating.outdated Outdating.cumLevel Population.outdate
    Population.level Outdating.orderUpTo
  rw [onHand_eq]
  congr 2
  split_ifs <;> first | rfl | omega

theorem periodCost_eq (c : Outdating.Params) (θ : ℝ≥0) (ψ : Lifetime.Policy c.m)
    (π : Population.Policy c.m) (h : Agrees ψ π) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Lifetime.periodCost (toL c θ) ψ d t = Outdating.periodCost c θ π d t := by
  unfold Lifetime.periodCost Outdating.periodCost
  rw [upTo_eq ψ π h, outdated_eq ψ π h]
  have hh : 0 ≤ c.h := c.h_pos.le
  have hp : 0 ≤ c.p := c.p_pos.le
  simp only [toL]
  rw [ENNReal.ofReal_mul hh, ENNReal.ofReal_mul hp, ENNReal.ofReal_mul (NNReal.coe_nonneg θ),
    ← coe_tsub, ← coe_tsub,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal]

theorem policyCost_eq (P : CappedBaseStock.DemandLaw) (c : Outdating.Params) (θ : ℝ≥0)
    (ψ : Lifetime.Policy c.m) (π : Population.Policy c.m) (h : Agrees ψ π) :
    Lifetime.policyCost P (toL c θ) ψ = Outdating.policyCost P c θ π := by
  unfold Lifetime.policyCost Lifetime.cesaroLimsup Outdating.policyCost
  simp_rw [periodCost_eq c θ ψ π h]

/-- Lift of an `ℝ≥0`-state policy to a real-state policy. -/
def lift {m : ℕ} (π : Population.Policy m) : Lifetime.Policy m where
  φ t x := π.φ t (fun j => (x j).toNNReal)
  measurable_φ t := (π.measurable_φ t).comp
    (measurable_pi_lambda _ fun j => (measurable_pi_apply j).real_toNNReal)

theorem agrees_lift {m : ℕ} (π : Population.Policy m) : Agrees (lift π) π := by
  intro t x
  simp [lift, emb]

theorem agrees_baseStock (m : ℕ) (S : ℝ≥0) :
    Agrees (Lifetime.baseStock m S) (Outdating.baseStock m S) := by
  intro t x
  simp only [Lifetime.baseStock, Outdating.baseStock, topLevel_emb, onHand_eq]
  rw [NNReal.sub_def]

theorem OPT_le (P : CappedBaseStock.DemandLaw) (c : Outdating.Params) (θ : ℝ≥0) :
    Lifetime.OPT P (toL c θ) ≤ Outdating.OPT P c θ := by
  unfold Outdating.OPT
  refine le_iInf fun π => ?_
  rw [← policyCost_eq P c θ (lift π) π (agrees_lift π)]
  exact iInf_le (fun ψ : Lifetime.Policy c.m => Lifetime.policyCost P (toL c θ) ψ) (lift π)

theorem bsCost_eq (P : CappedBaseStock.DemandLaw) (c : Outdating.Params) (θ : ℝ≥0) (S : ℝ≥0) :
    Lifetime.bsCost P (toL c θ) S = Outdating.bsCost P c θ S :=
  policyCost_eq P c θ _ _ (agrees_baseStock c.m S)

theorem run_zero {m : ℕ} (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Population.run (Outdating.baseStock m 0) d t = Population.emptyState m := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have : Population.run (Outdating.baseStock m 0) d (t + 1) =
        Population.next (Population.run (Outdating.baseStock m 0) d t)
          ((Outdating.baseStock m 0).φ t (Population.run (Outdating.baseStock m 0) d t)) (d t) := rfl
    rw [this, ih]
    funext i
    simp [Population.next, Population.level, Population.outdate, Population.topLevel,
      Population.emptyState, Outdating.baseStock]

theorem periodCost_zero (c : Outdating.Params) (θ : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    Outdating.periodCost c θ (Outdating.baseStock c.m 0) d t =
      ENNReal.ofReal c.p * ((d t : ℝ≥0) : ℝ≥0∞) := by
  have h1 : Outdating.orderUpTo (Outdating.baseStock c.m 0) d t = 0 := by
    unfold Outdating.orderUpTo
    rw [run_zero]
    simp [Outdating.onHand, Population.emptyState, Outdating.baseStock]
  have h2 : Outdating.outdatedAt (Outdating.baseStock c.m 0) d t = 0 := by
    unfold Outdating.outdatedAt Outdating.outdated Outdating.cumLevel
    rw [h1, run_zero]
    split_ifs <;> simp [Population.emptyState]
  unfold Outdating.periodCost
  rw [h1, h2]
  simp

theorem lintegral_coord (P : CappedBaseStock.DemandLaw) (t : ℕ) :
    ∫⁻ d, ((d t : ℝ≥0) : ℝ≥0∞) ∂CappedBaseStock.demandPathLaw P < ⊤ := by
  have hmap : (CappedBaseStock.demandPathLaw P).map (fun d => d t) = P.law :=
    Measure.infinitePi_map_eval _ t
  have e : ∫⁻ d, ((d t : ℝ≥0) : ℝ≥0∞) ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ x, ((x : ℝ≥0) : ℝ≥0∞) ∂P.law := by
    rw [← hmap, lintegral_map (by fun_prop) (measurable_pi_apply t)]
  rw [e]
  have := P.finiteMean.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  convert this using 2 with x
  simp

theorem OPT_lt_top (P : CappedBaseStock.DemandLaw) (c : Outdating.Params) (θ : ℝ≥0) :
    Outdating.OPT P c θ < ⊤ := by
  set I := ∫⁻ d, ((d 0 : ℝ≥0) : ℝ≥0∞) ∂CappedBaseStock.demandPathLaw P
  have hI : ∀ t, ∫⁻ d, ((d t : ℝ≥0) : ℝ≥0∞) ∂CappedBaseStock.demandPathLaw P = I := by
    intro t
    have hmap : ∀ s, (CappedBaseStock.demandPathLaw P).map (fun d => d s) = P.law :=
      fun s => Measure.infinitePi_map_eval _ s
    rw [← lintegral_map (f := fun x : ℝ≥0 => (x : ℝ≥0∞)) (by fun_prop) (measurable_pi_apply t),
      hmap t, ← hmap 0, lintegral_map (by fun_prop) (measurable_pi_apply 0)]
  set K := ENNReal.ofReal c.p * I
  have hK : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_coord P 0)
  have hcost : Outdating.policyCost P c θ (Outdating.baseStock c.m 0) = K := by
    unfold Outdating.policyCost
    simp_rw [periodCost_zero]
    have : ∀ T : ℕ, (∑ t ∈ Finset.range (T + 1),
        ∫⁻ d, ENNReal.ofReal c.p * ((d t : ℝ≥0) : ℝ≥0∞) ∂CappedBaseStock.demandPathLaw P) /
          ((T : ℝ≥0∞) + 1) = K := by
      intro T
      have e : ∀ t, ∫⁻ d, ENNReal.ofReal c.p * ((d t : ℝ≥0) : ℝ≥0∞)
          ∂CappedBaseStock.demandPathLaw P = K := by
        intro t
        rw [lintegral_const_mul _ (by fun_prop), hI t]
      simp_rw [e]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rw [mul_comm]
      exact ENNReal.mul_div_cancel_right (by simp) (by simp)
    simp_rw [this]
    exact limsup_const K
  calc Outdating.OPT P c θ ≤ Outdating.policyCost P c θ (Outdating.baseStock c.m 0) :=
        iInf_le _ _
    _ = K := hcost
    _ < ⊤ := hK

end PBS4R

open PerishBaseStock.Outdating PBS4R in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (St : ℝ≥0 → ℝ≥0)
    (hSt : ∀ θ : ℝ≥0, IsHeurMin P c θ (St θ)) :
    (∀ θ : ℝ≥0, bsCost P c θ (St θ) < ⊤) ∧
      Tendsto (fun θ : ℝ≥0 => (bsCost P c θ (St θ)).toReal - (OPT P c θ).toReal)
        atTop (𝓝 0) := by
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast c.one_le_m
  set E : ℝ≥0 → ℝ := fun θ => excessOverLifetimeDemand P c (St θ) with hE
  have hE0 : ∀ θ, 0 ≤ E θ := fun θ => integral_nonneg fun _ => le_max_right _ _
  set B : ℝ≥0 → ℝ := fun θ => ((c.m : ℝ) - 1) * (θ : ℝ) / c.m * E θ with hB
  have hB0 : ∀ θ, 0 ≤ B θ := fun θ => by
    have := hE0 θ
    have : 0 ≤ (c.m : ℝ) - 1 := by linarith
    simp only [hB]; positivity
  have hBle : ∀ θ, B θ ≤ (θ : ℝ) * E θ := fun θ => by
    simp only [hB]
    have hθ : 0 ≤ (θ : ℝ) := θ.2
    have h1 : ((c.m : ℝ) - 1) * (θ : ℝ) / c.m ≤ θ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    exact mul_le_mul_of_nonneg_right h1 (hE0 θ)
  have key : ∀ θ : ℝ≥0, bsCost P c θ (St θ) ≤ OPT P c θ + ENNReal.ofReal (B θ) := by
    intro θ
    have h21 := PerishBaseStock.Lifetime.eq_21_gap_bound P (toL c θ) (St θ) (fun S' => hSt θ S')
    rw [bsCost_eq] at h21
    exact h21.trans (add_le_add (OPT_le P c θ) le_rfl)
  have hfin : ∀ θ : ℝ≥0, bsCost P c θ (St θ) < ⊤ := fun θ =>
    lt_of_le_of_lt (key θ) (ENNReal.add_lt_top.2 ⟨OPT_lt_top P c θ, ENNReal.ofReal_lt_top⟩)
  refine ⟨hfin, ?_⟩
  have hOle : ∀ θ : ℝ≥0, OPT P c θ ≤ bsCost P c θ (St θ) := fun θ =>
    iInf_le (fun π => policyCost P c θ π) (baseStock c.m (St θ))
  have lower : ∀ θ : ℝ≥0, 0 ≤ (bsCost P c θ (St θ)).toReal - (OPT P c θ).toReal := fun θ => by
    have := ENNReal.toReal_mono (hfin θ).ne (hOle θ)
    linarith
  have upper : ∀ θ : ℝ≥0, (bsCost P c θ (St θ)).toReal - (OPT P c θ).toReal ≤ (θ : ℝ) * E θ :=
    fun θ => by
    have h1 := ENNReal.toReal_mono
      (ENNReal.add_lt_top.2 ⟨OPT_lt_top P c θ, ENNReal.ofReal_lt_top⟩).ne (key θ)
    rw [ENNReal.toReal_add (OPT_lt_top P c θ).ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hB0 θ)] at h1
    linarith [hBle θ]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (eq_24 P c St hSt)
    lower upper
