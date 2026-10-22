-- Prove2me | solution 1 for SocialManip.Beliefs.BU_converges_ae
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:06:42.426886+00:00
-- url     : https://prove2.me/submissions/f8829411-ee1f-4dbe-8954-abc3f5646250

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace SMAuxBU
open SocialManip.Beliefs

theorem bus_formula (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (zS zR : ℕ) :
    BUS p q zS zR = (1 + (1 - q) / q *
      Real.exp (-(Real.log p - Real.log (1 - p)) * ((zS : ℝ) - zR)))⁻¹ := by
  have h1p : 0 < 1 - p := by linarith
  have e1 : Real.exp (-(Real.log p - Real.log (1 - p)) * ((zS : ℝ) - zR)) =
      (p ^ zR * (1 - p) ^ zS) / (p ^ zS * (1 - p) ^ zR) := by
    have : -(Real.log p - Real.log (1 - p)) * ((zS : ℝ) - zR) =
        ((zR : ℝ) * Real.log p + (zS : ℝ) * Real.log (1 - p)) -
          ((zS : ℝ) * Real.log p + (zR : ℝ) * Real.log (1 - p)) := by ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hp0, Real.exp_log h1p]
  rw [e1]
  unfold BUS
  have : 0 < p ^ zS * (1 - p) ^ zR := by positivity
  have : 0 < p ^ zR * (1 - p) ^ zS := by positivity
  have : 0 < 1 - q := by linarith
  field_simp

theorem countS_succ (g : ℕ → State) (t : ℕ) :
    countS g (t + 1) = countS g t + if g (t + 1) = State.S then 1 else 0 := by
  unfold countS
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]; simp
  · rfl

theorem countR_succ (g : ℕ → State) (t : ℕ) :
    countR g (t + 1) = countR g t + if g (t + 1) = State.S then 0 else 1 := by
  unfold countR
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  rcases hg : g (t + 1) with _ | _
  · simp
  · rw [if_pos rfl, Finset.card_insert_of_notMem] <;> simp

theorem count_diff (g : ℕ → State) (t : ℕ) :
    ((countS g t : ℝ) - countR g t) =
      ∑ k ∈ Finset.range t, (if g (k + 1) = State.S then (1 : ℝ) else -1) := by
  induction t with
  | zero => simp [countS, countR]
  | succ t ih =>
    rw [countS_succ, countR_succ, Finset.sum_range_succ, ← ih]
    split_ifs <;> push_cast <;> ring

theorem rho_ne (p lam lamStar : ℝ) (y yhat : State) (xi : Bool)
    (hp : 1 / 2 < p) (hlam : 0 < lam) (hlamStar : 0 < lamStar)
    (hA1i : p < (lamStar + lam) / (2 * lam)) :
    signalProbS p lam lamStar y yhat xi ≠ 1 / 2 := by
  have h2 : 2 * lam * p < lamStar + lam := by
    rw [lt_div_iff₀ (by positivity)] at hA1i; linarith
  have hs : 0 < lam + lamStar := by linarith
  intro h
  unfold signalProbS organicProbS at h
  cases xi <;> cases y <;> cases yhat <;> simp at h
  all_goals
    first
    | linarith
    | (rw [div_eq_iff hs.ne'] at h; nlinarith)

end SMAuxBU

open SocialManip.Beliefs

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p q lam lamStar : ℝ) (y yhat y' : State) (xi : Bool)
    (hq : 0 < q ∧ q < 1) (hp : 1 / 2 ≤ p ∧ p < 1) (hlam : 0 < lam) (hlamStar : 0 < lamStar)
    (hA1i : p < (lamStar + lam) / (2 * lam))
    (h : ℕ → Ω → State) (hm : ∀ τ, Measurable (h τ)) (hind : iIndepFun h P)
    (hlaw : ∀ τ, P {ω | h τ ω = State.S} =
      ENNReal.ofReal (signalProbS p lam lamStar y yhat xi)) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, Tendsto (fun t => BU p q (fun τ => h τ ω) t y') atTop (𝓝 c) := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hp0, hp1⟩ := hp
  have hpp : 0 < p := by linarith
  set K := (1 - q) / q with hK
  have hKpos : 0 < K := div_pos (by linarith) hq0
  set L := Real.log p - Real.log (1 - p) with hL
  -- the face-value posterior of `S` in closed form
  set Sω : Ω → ℕ → ℝ := fun ω t =>
    ∑ k ∈ Finset.range t, (if h (k + 1) ω = State.S then (1 : ℝ) else -1) with hSω
  have hform : ∀ ω t, BUS p q (countS (fun τ => h τ ω) t) (countR (fun τ => h τ ω) t) =
      (1 + K * Real.exp (-L * Sω ω t))⁻¹ := by
    intro ω t
    rw [SMAuxBU.bus_formula p q hpp hp1 hq0 hq1, SMAuxBU.count_diff]
  -- it suffices to treat `y' = S`
  suffices hS : ∃ c : ℝ, ∀ᵐ ω ∂P, Tendsto (fun t => (1 + K * Real.exp (-L * Sω ω t))⁻¹)
      atTop (𝓝 c) by
    obtain ⟨c, hc⟩ := hS
    by_cases hy : y' = State.S
    · refine ⟨c, ?_⟩
      filter_upwards [hc] with ω hω
      simpa [BU, hy, hform] using hω
    · refine ⟨1 - c, ?_⟩
      filter_upwards [hc] with ω hω
      have := hω.const_sub 1
      simpa [BU, hy, hform] using this
  rcases eq_or_lt_of_le hp0 with hp12 | hp12
  · -- `p = 1/2`: the posterior is constantly the prior
    have hL0 : L = 0 := by
      rw [hL, ← hp12]; norm_num
    refine ⟨(1 + K)⁻¹, Eventually.of_forall fun ω => ?_⟩
    simp [hL0]
  -- `p > 1/2`
  have hLpos : 0 < L := by
    rw [hL, sub_pos]
    exact Real.log_lt_log (by linarith) (by linarith)
  -- the ±1 increments
  set g : State → ℝ := fun s => if s = State.S then 1 else -1 with hg
  have hgm : Measurable g := measurable_of_finite g
  set X : ℕ → Ω → ℝ := fun k ω => g (h (k + 1) ω) with hX
  have hXm : ∀ k, Measurable (X k) := fun k => hgm.comp (hm (k + 1))
  have hint : Integrable (X 0) P := by
    refine Integrable.of_bound (hXm 0).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    simp only [hX, hg]; split_ifs <;> simp
  have hindep : Pairwise (Function.onFun (fun f₁ f₂ => IndepFun f₁ f₂ P) X) := by
    intro i j hij
    exact (hind.indepFun (by omega : i + 1 ≠ j + 1)).comp hgm hgm
  have hmapeq : ∀ τ, Measure.map (h τ) P = Measure.map (h 1) P := by
    intro τ
    rw [Measure.ext_iff_singleton]
    intro s
    rw [Measure.map_apply (hm τ) (measurableSet_singleton s),
      Measure.map_apply (hm 1) (measurableSet_singleton s)]
    have hSset : ∀ τ, h τ ⁻¹' {State.S} = {ω | h τ ω = State.S} := fun τ => rfl
    have hRset : ∀ τ, h τ ⁻¹' {State.R} = {ω | h τ ω = State.S}ᶜ := by
      intro τ; ext ω; cases hω : h τ ω <;> simp [hω]
    cases s
    · rw [hSset, hSset, hlaw, hlaw]
    · rw [hRset, hRset,
        prob_compl_eq_one_sub (s := {ω | h τ ω = State.S}) ((hm τ) (measurableSet_singleton _)),
        prob_compl_eq_one_sub (s := {ω | h 1 ω = State.S}) ((hm 1) (measurableSet_singleton _)),
        hlaw, hlaw]
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := by
    intro k
    have : IdentDistrib (h (k + 1)) (h 1) P P :=
      ⟨(hm _).aemeasurable, (hm _).aemeasurable, hmapeq (k + 1)⟩
    exact this.comp hgm
  have hslln := ProbabilityTheory.strong_law_ae X hint hindep hident
  -- the mean of the increments is `2ρ - 1 ≠ 0`
  set ρ' := P.real {ω | h 1 ω = State.S} with hρ'
  have hρ'eq : ρ' = max (signalProbS p lam lamStar y yhat xi) 0 := by
    rw [hρ', measureReal_def, hlaw, ENNReal.toReal_ofReal']
  have hρne : ρ' ≠ 1 / 2 := by
    intro h12
    rw [hρ'eq] at h12
    have hne := SMAuxBU.rho_ne p lam lamStar y yhat xi hp12 hlam hlamStar hA1i
    rcases le_total (signalProbS p lam lamStar y yhat xi) 0 with hle | hle
    · rw [max_eq_right hle] at h12; norm_num at h12
    · rw [max_eq_left hle] at h12; exact hne h12
  have hmean : P[X 0] = 2 * ρ' - 1 := by
    have hX0 : X 0 = g ∘ h 1 := rfl
    rw [hX0, show (∫ ω, (g ∘ h 1) ω ∂P) = ∫ ω, g (h 1 ω) ∂P from rfl,
      ← integral_map (hm 1).aemeasurable hgm.aestronglyMeasurable,
      integral_fintype (Integrable.of_finite)]
    have hsum : ∀ f : State → ℝ, ∑ s, f s = f State.S + f State.R := by
      intro f
      show ∑ s ∈ ({State.S, State.R} : Finset State), f s = _
      rw [Finset.sum_pair (by decide)]
    rw [hsum]
    have h1 : (Measure.map (h 1) P).real {State.S} = ρ' := by
      rw [measureReal_def, Measure.map_apply (hm 1) (measurableSet_singleton _)]; rfl
    have h2 : (Measure.map (h 1) P).real {State.R} = 1 - ρ' := by
      rw [measureReal_def, Measure.map_apply (hm 1) (measurableSet_singleton _)]
      have : h 1 ⁻¹' {State.R} = {ω | h 1 ω = State.S}ᶜ := by
        ext ω; cases hω : h 1 ω <;> simp [hω]
      rw [this, ← measureReal_def, measureReal_compl (s := {ω | h 1 ω = State.S}) ((hm 1) (measurableSet_singleton _)),
        probReal_univ]
    rw [h1, h2]
    simp [hg]
    ring
  rw [hmean] at hslln
  have hm0 : 2 * ρ' - 1 ≠ 0 := by
    intro h0; apply hρne; linarith
  -- deterministic consequence
  have hSeq : ∀ ω t, Sω ω t = (t : ℝ) * ((t : ℝ)⁻¹ • ∑ i ∈ Finset.range t, X i ω) := by
    intro ω t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp [hSω]
    · rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · refine ⟨0, ?_⟩
    filter_upwards [hslln] with ω hω
    have h1 : Tendsto (fun t => Sω ω t) atTop atBot := by
      simp_rw [hSeq]
      exact tendsto_natCast_atTop_atTop.atTop_mul_neg hneg hω
    have h2 : Tendsto (fun t => -L * Sω ω t) atTop atTop := by
      have := (tendsto_neg_atBot_atTop.comp h1).const_mul_atTop hLpos
      refine this.congr fun t => ?_
      show L * -(Sω ω t) = -L * Sω ω t
      ring
    have h3 : Tendsto (fun t => 1 + K * Real.exp (-L * Sω ω t)) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((Real.tendsto_exp_atTop.comp h2).const_mul_atTop hKpos)
    exact h3.inv_tendsto_atTop
  · refine ⟨1, ?_⟩
    filter_upwards [hslln] with ω hω
    have h1 : Tendsto (fun t => Sω ω t) atTop atTop := by
      simp_rw [hSeq]
      exact tendsto_natCast_atTop_atTop.atTop_mul_pos hpos hω
    have h2 : Tendsto (fun t => -L * Sω ω t) atTop atBot :=
      h1.const_mul_atTop_of_neg (by linarith)
    have h3 : Tendsto (fun t => 1 + K * Real.exp (-L * Sω ω t)) atTop (𝓝 (1 + K * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp h2))
    have h4 := h3.inv₀ (by simp)
    simpa using h4
