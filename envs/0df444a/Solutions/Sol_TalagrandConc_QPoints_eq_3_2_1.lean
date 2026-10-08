-- Prove2me | solution 1 for TalagrandConc.QPoints.eq_3_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:25:11.577519+00:00
-- url     : https://prove2.me/submissions/0808a029-16c7-4622-b08b-20d3e2621a35

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic
import Definitions.Def_TalagrandConc_QPoints_aConst



namespace TalagrandConc.QPoints

open MeasureTheory Set
open scoped ENNReal
open Classical

lemma uncaptured_eq_sum {Ω : Type*} {N q : ℕ} (y : Fin q → Fin N → Ω) (x : Fin N → Ω) :
    uncaptured y x = ∑ i : Fin N, (if ∀ j : Fin q, x i ≠ y j i then 1 else 0) := by
  unfold uncaptured
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

lemma uncaptured_snoc {Ω : Type*} {N q : ℕ} (y' : Fin q → Fin N → Ω) (ω' : Fin q → Ω)
    (x : Fin N → Ω) (ω : Ω) :
    uncaptured (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω))
        (Fin.snoc x ω : Fin (N + 1) → Ω) =
      uncaptured y' x + (if ∀ j : Fin q, ω ≠ ω' j then 1 else 0) := by
  rw [uncaptured_eq_sum, uncaptured_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma qDist_le_of_mem {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (y : Fin q → Fin N → Ω) (hy : ∀ j, y j ∈ A j) : qDist A x ≤ (uncaptured y x : ℕ∞) := by
  unfold qDist
  exact iInf₂_le y hy

lemma le_qDist {Ω : Type*} {N q : ℕ} (A : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω) (c : ℕ∞)
    (h : ∀ y : Fin q → Fin N → Ω, (∀ j, y j ∈ A j) → c ≤ (uncaptured y x : ℕ∞)) :
    c ≤ qDist A x := by
  unfold qDist
  exact le_iInf₂ h

lemma qDist_anti {Ω : Type*} {N q : ℕ} (A A' : Fin q → Set (Fin N → Ω)) (x : Fin N → Ω)
    (h : ∀ i, A i ⊆ A' i) : qDist A' x ≤ qDist A x := by
  apply le_qDist
  intro y hy
  exact qDist_le_of_mem A' x y (fun j => h j (hy j))

theorem eq_3_1_6_core {Ω : Type*} {N q : ℕ} (hq : 2 ≤ q) (A : Fin q → Set (Fin (N + 1) → Ω))
    (x : Fin N → Ω) (ω : Ω) :
    qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤ 1 + qDist (fun i => projLast (A i)) x ∧
      ∀ j : Fin q, qDist A (Fin.snoc x ω : Fin (N + 1) → Ω) ≤
        qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x := by
  classical
  constructor
  · unfold qDist
    rw [ENat.add_iInf₂]
    refine le_iInf₂ fun y' hy' => ?_
    choose ω' hω' using hy'
    refine le_trans (iInf₂_le (fun j => (Fin.snoc (y' j) (ω' j) : Fin (N + 1) → Ω)) hω') ?_
    rw [uncaptured_snoc]
    push_cast
    split_ifs <;> simp [add_comm]
  · intro j
    apply le_qDist
    intro y' hy'
    have hj : y' j ∈ sliceAt (A j) ω := by simpa using hy' j
    have hother : ∀ i, i ≠ j → y' i ∈ projLast (A i) := by
      intro i hi
      have := hy' i
      rwa [Function.update_of_ne hi] at this
    let ω' : Fin q → Ω := fun i => if h : i = j then ω else Classical.choose (hother i h)
    have hmem : ∀ i, (Fin.snoc (y' i) (ω' i) : Fin (N + 1) → Ω) ∈ A i := by
      intro i
      by_cases h : i = j
      · subst h
        simp only [ω', dif_pos]
        exact hj
      · simp only [ω', dif_neg h]
        exact Classical.choose_spec (hother i h)
    refine le_trans (qDist_le_of_mem A _ _ hmem) ?_
    rw [uncaptured_snoc]
    have : ¬ ∀ i : Fin q, ω ≠ ω' i := by
      push Not
      exact ⟨j, by simp [ω']⟩
    simp [this]


/-- The function `ψ(x) = x + q α x^{-1/α}`. -/
noncomputable def psiQ (q : ℕ) (α : ℝ) (x : ℝ) : ℝ := x + (q : ℝ) * α * x ^ (-(1 / α))

lemma psiQ_hasDerivAt (q : ℕ) (α : ℝ) (hα : 1 < α) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (psiQ q α) (1 - (q : ℝ) * x ^ (-(1 / α) - 1)) x := by
  have hα0 : α ≠ 0 := by positivity
  have h1 := Real.hasDerivAt_rpow_const (x := x) (p := -(1 / α)) (Or.inl hx.ne')
  have h2 := (hasDerivAt_id x).add (h1.const_mul ((q : ℝ) * α))
  refine h2.congr_deriv ?_
  field_simp
  ring

lemma psiQ_continuousOn (q : ℕ) (α : ℝ) (hα : 1 < α) {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) :
    ContinuousOn (psiQ q α) s :=
  fun x hx => (psiQ_hasDerivAt q α hα (hs x hx)).continuousAt.continuousWithinAt

/-- The turning point `x₀ = q^{α/(α+1)}`. -/
noncomputable def x0Q (q : ℕ) (α : ℝ) : ℝ := (q : ℝ) ^ (α / (α + 1))

lemma x0Q_pow (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    x0Q q α ^ (1 + 1 / α) = q := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  unfold x0Q
  rw [← Real.rpow_mul hq0]
  have : α / (α + 1) * (1 + 1 / α) = 1 := by
    field_simp
  rw [this, Real.rpow_one]

lemma one_lt_x0Q (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) : 1 < x0Q q α := by
  unfold x0Q
  apply Real.one_lt_rpow
  · exact_mod_cast (by omega : 1 < q)
  · positivity

/-- Sign of the derivative. -/
lemma deriv_sign (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) {x : ℝ} (hx : 0 < x) :
    (1 - (q : ℝ) * x ^ (-(1 / α) - 1) < 0 ↔ x < x0Q q α) ∧
    (0 < 1 - (q : ℝ) * x ^ (-(1 / α) - 1) ↔ x0Q q α < x) := by
  have hβ : (0 : ℝ) < 1 + 1 / α := by positivity
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have e1 : x ^ (-(1 / α) - 1) = (x ^ (1 + 1 / α))⁻¹ := by
    rw [← Real.rpow_neg hx.le]
    congr 1
    ring
  have hxp : 0 < x ^ (1 + 1 / α) := Real.rpow_pos_of_pos hx _
  have hx0pos : 0 < x0Q q α := by
    have := one_lt_x0Q q α hα hq; linarith
  have key : x < x0Q q α ↔ x ^ (1 + 1 / α) < q := by
    rw [← x0Q_pow q α hα hq]
    exact (Real.rpow_lt_rpow_iff hx.le hx0pos.le hβ).symm
  have key2 : x0Q q α < x ↔ (q : ℝ) < x ^ (1 + 1 / α) := by
    rw [← x0Q_pow q α hα hq]
    exact (Real.rpow_lt_rpow_iff hx0pos.le hx.le hβ).symm
  rw [e1, key, key2]
  constructor
  · rw [sub_neg, ← div_eq_mul_inv, lt_div_iff₀ hxp, one_mul]
  · rw [sub_pos, ← div_eq_mul_inv, div_lt_iff₀ hxp, one_mul]

lemma psiQ_strictAntiOn (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    StrictAntiOn (psiQ q α) (Icc 1 (x0Q q α)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact psiQ_continuousOn q α hα fun x hx => by linarith [hx.1]
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(psiQ_hasDerivAt q α hα hx0).deriv]
    exact (deriv_sign q α hα hq hx0).1.2 hx.2

lemma psiQ_strictMonoOn (q : ℕ) (α : ℝ) (hα : 1 < α) (hq : 2 ≤ q) :
    StrictMonoOn (psiQ q α) (Ici (x0Q q α)) := by
  have h1 := one_lt_x0Q q α hα hq
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact psiQ_continuousOn q α hα fun x hx => by
      simp only [mem_Ici] at hx; linarith
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := by simp only [mem_Ioi] at hx; linarith
    rw [(psiQ_hasDerivAt q α hα hx0).deriv]
    exact (deriv_sign q α hα hq hx0).2.2 hx

lemma psiQ_one (q : ℕ) (α : ℝ) : psiQ q α 1 = 1 + (q : ℝ) * α := by
  simp [psiQ]

lemma self_le_psiQ (q : ℕ) (α : ℝ) (hα : 1 < α) {x : ℝ} (hx : 0 < x) : x ≤ psiQ q α x := by
  unfold psiQ
  have : 0 ≤ (q : ℝ) * α * x ^ (-(1 / α)) := by
    have := Real.rpow_nonneg hx.le (-(1 / α))
    positivity
  linarith


/-- All facts about `aConst` in one place. -/
theorem aConst_facts (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) :
    1 < aConst q α ∧ psiQ q α (aConst q α) = 1 + (q : ℝ) * α ∧ x0Q q α < aConst q α ∧
      ∀ x : ℝ, 1 < x → psiQ q α x = 1 + (q : ℝ) * α → x = aConst q α := by
  set c : ℝ := 1 + (q : ℝ) * α with hc
  set x₀ := x0Q q α with hx₀
  have h1 := one_lt_x0Q q α hα hq
  have hanti := psiQ_strictAntiOn q α hα hq
  have hmono := psiQ_strictMonoOn q α hα hq
  have hψ1 : psiQ q α 1 = c := psiQ_one q α
  have hψx₀ : psiQ q α x₀ < c := by
    rw [← hψ1]
    exact hanti ⟨le_rfl, h1.le⟩ ⟨h1.le, le_rfl⟩ h1
  set M := max x₀ c with hM
  have hx₀M : x₀ ≤ M := le_max_left _ _
  have hψM : c ≤ psiQ q α M :=
    le_trans (le_max_right _ _) (self_le_psiQ q α hα (by linarith [le_max_left x₀ c]))
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc hx₀M
    (psiQ_continuousOn q α hα fun x hx => by linarith [hx.1]) ⟨hψx₀.le, hψM⟩
  have hrx₀ : x₀ < r := by
    rcases eq_or_lt_of_le hrI.1 with h | h
    · rw [← h] at hr; linarith
    · exact h
  have hr1 : 1 < r := by linarith
  set S : Set ℝ := {x : ℝ | 1 < x ∧ x + (q : ℝ) * α * x ^ (-(1 / α)) ≤ 1 + (q : ℝ) * α} with hS
  have hrS : r ∈ S := ⟨hr1, by change psiQ q α r ≤ c; rw [hr]⟩
  have hSle : ∀ x ∈ S, x ≤ r := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    change psiQ q α x ≤ c at hx2
    by_contra hcon
    push Not at hcon
    have : psiQ q α r < psiQ q α x := hmono (mem_Ici.2 hrx₀.le) (mem_Ici.2 (by linarith)) hcon
    linarith
  have haeq : aConst q α = r := by
    unfold aConst
    exact le_antisymm (csSup_le ⟨r, hrS⟩ hSle) (le_csSup ⟨r, hSle⟩ hrS)
  refine ⟨by rw [haeq]; exact hr1, by rw [haeq]; exact hr, by rw [haeq]; exact hrx₀, ?_⟩
  intro x hx1 hx2
  rw [haeq]
  rcases lt_or_ge x x₀ with hlt | hge
  · exfalso
    have : psiQ q α x < psiQ q α 1 := hanti ⟨le_rfl, h1.le⟩ ⟨hx1.le, hlt.le⟩ hx1
    linarith
  · exact hmono.injOn (mem_Ici.2 hge) (mem_Ici.2 hrx₀.le) (by rw [hx2, hr])

lemma psiQ_le_of_mem (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) {y : ℝ} (hy1 : 1 ≤ y)
    (hya : y ≤ aConst q α) : psiQ q α y ≤ 1 + (q : ℝ) * α := by
  obtain ⟨_, haeq, hx₀a, _⟩ := aConst_facts q hq α hα
  rcases le_or_gt y (x0Q q α) with h | h
  · have := (psiQ_strictAntiOn q α hα hq).antitoneOn ⟨le_rfl, (one_lt_x0Q q α hα hq).le⟩
      ⟨hy1, h⟩ hy1
    rw [psiQ_one] at this
    exact this
  · have := (psiQ_strictMonoOn q α hα hq).monotoneOn (mem_Ici.2 h.le)
      (mem_Ici.2 hx₀a.le) hya
    rw [haeq] at this
    exact this

/-- The chord inequality `x^{-α} ≤ 1 + qα(1 - x)` on `[a^{-1/α}, 1]`. -/
lemma chord_ineq (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) {x : ℝ}
    (hxb : aConst q α ^ (-(1 / α)) ≤ x) (hx1 : x ≤ 1) :
    x ^ (-α) ≤ 1 + (q : ℝ) * α * (1 - x) := by
  have ha1 : 1 < aConst q α := (aConst_facts q hq α hα).1
  have ha0 : 0 < aConst q α := by linarith
  have hb0 : 0 < aConst q α ^ (-(1 / α)) := Real.rpow_pos_of_pos ha0 _
  have hx0 : 0 < x := lt_of_lt_of_le hb0 hxb
  have hα0 : α ≠ 0 := by positivity
  set y := x ^ (-α) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
  have hya : y ≤ aConst q α := by
    calc y ≤ (aConst q α ^ (-(1 / α))) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hb0 hxb (by linarith)
      _ = aConst q α := by
          rw [← Real.rpow_mul ha0.le]
          have : -(1 / α) * -α = 1 := by field_simp
          rw [this, Real.rpow_one]
  have hyx : y ^ (-(1 / α)) = x := by
    rw [hy, ← Real.rpow_mul hx0.le]
    have : -α * -(1 / α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have := psiQ_le_of_mem q hq α hα hy1 hya
  unfold psiQ at this
  rw [hyx] at this
  linarith

/-- `(1 + p(1-u)) u^p ≤ 1` for `0 ≤ u ≤ 1`, `1 ≤ p`. -/
lemma key_rpow_ineq (p : ℝ) (hp : 1 ≤ p) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + p * (1 - u)) * u ^ p ≤ 1 := by
  set t := 1 - u with ht
  have hu : u = 1 - t := by rw [ht]; ring
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hb : 1 + p * t ≤ (1 + t) ^ p := one_add_mul_self_le_rpow_one_add (by linarith) hp
  rw [hu]
  calc (1 + p * t) * (1 - t) ^ p ≤ (1 + t) ^ p * (1 - t) ^ p :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) p)
    _ = (1 - t ^ 2) ^ p := by rw [← Real.mul_rpow (by linarith) (by linarith)]; ring_nf
    _ ≤ 1 := Real.rpow_le_one (by nlinarith) (by nlinarith) (by linarith)

theorem lemma_alpha_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, aConst q α ^ (-(1 / α)) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, g ω ^ (-α) ∂μ) * ((∫ ω, g ω ∂μ) ^ α) ^ q ≤ 1 := by
  have ha1 : 1 < aConst q α := (aConst_facts q hq α hα).1
  have ha0 : 0 < aConst q α := by linarith
  have hb0 : 0 < aConst q α ^ (-(1 / α)) := Real.rpow_pos_of_pos ha0 _
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hb0 (hlow ω)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqα : (1 : ℝ) ≤ q * α := by nlinarith
  have hα0 : α ≠ 0 := by positivity
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hgpos ω, hup ω]
  have hbound : ∀ ω, g ω ^ (-α) ≤ aConst q α := by
    intro ω
    calc g ω ^ (-α) ≤ (aConst q α ^ (-(1 / α))) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hb0 (hlow ω) (by linarith)
      _ = aConst q α := by
          rw [← Real.rpow_mul ha0.le]
          have : -(1 / α) * -α = 1 := by field_simp
          rw [this, Real.rpow_one]
  have hint_inv : Integrable (fun ω => g ω ^ (-α)) μ := by
    refine Integrable.of_bound (hg.pow_const (-α)).aestronglyMeasurable (aConst q α)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := Real.rpow_nonneg (hgpos ω).le (-α); linarith
    · exact hbound ω
  have hpt : ∀ ω, g ω ^ (-α) ≤ (1 + (q : ℝ) * α) - q * α * g ω := by
    intro ω
    have := chord_ineq q hq α hα (hlow ω) (hup ω)
    linarith
  have h1 : ∫ ω, g ω ^ (-α) ∂μ ≤ ∫ ω, ((1 + (q : ℝ) * α) - q * α * g ω) ∂μ := by
    refine integral_mono hint_inv ?_ hpt
    exact (integrable_const _).sub (hint_g.const_mul _)
  have h2 : ∫ ω, ((1 + (q : ℝ) * α) - q * α * g ω) ∂μ = (1 + (q : ℝ) * α) - q * α * ∫ ω, g ω ∂μ := by
    rw [integral_sub (integrable_const _) (hint_g.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hu0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg fun ω => (hgpos ω).le
  have hu1 : ∫ ω, g ω ∂μ ≤ 1 := by
    have := integral_mono hint_g (integrable_const (1 : ℝ)) hup
    simpa using this
  have hA : 0 ≤ ((∫ ω, g ω ∂μ) ^ α) ^ q := pow_nonneg (Real.rpow_nonneg hu0 α) q
  have hpow : ((∫ ω, g ω ∂μ) ^ α) ^ q = (∫ ω, g ω ∂μ) ^ ((q : ℝ) * α) := by
    rw [mul_comm, Real.rpow_mul hu0, Real.rpow_natCast]
  calc (∫ ω, g ω ^ (-α) ∂μ) * ((∫ ω, g ω ∂μ) ^ α) ^ q
      ≤ ((1 + (q : ℝ) * α) - q * α * ∫ ω, g ω ∂μ) * ((∫ ω, g ω ∂μ) ^ α) ^ q := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hA
    _ = (1 + (q : ℝ) * α * (1 - ∫ ω, g ω ∂μ)) * (∫ ω, g ω ∂μ) ^ ((q : ℝ) * α) := by
        rw [hpow]; ring
    _ ≤ 1 := key_rpow_ineq _ hqα _ hu0 hu1

theorem lemma_alpha_ennreal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (h : Ω → ℝ≥0∞)
    (hh : Measurable h) (hlow : ∀ ω, ENNReal.ofReal (aConst q α ^ (-(1 / α))) ≤ h ω)
    (hup : ∀ ω, h ω ≤ 1) :
    (∫⁻ ω, (h ω ^ α)⁻¹ ∂μ) * ((∫⁻ ω, h ω ∂μ) ^ α) ^ q ≤ 1 := by
  have ha1 : 1 < aConst q α := (aConst_facts q hq α hα).1
  have ha0 : 0 < aConst q α := by linarith
  have hb0 : 0 < aConst q α ^ (-(1 / α)) := Real.rpow_pos_of_pos ha0 _
  have hα0 : 0 ≤ α := by linarith
  have hne : ∀ ω, h ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top ENNReal.one_ne_top (hup ω)
  set g : Ω → ℝ := fun ω => (h ω).toReal with hg_def
  have hg : Measurable g := ENNReal.measurable_toReal.comp hh
  have hglow : ∀ ω, aConst q α ^ (-(1 / α)) ≤ g ω := by
    intro ω
    have := ENNReal.toReal_mono (hne ω) (hlow ω)
    rwa [ENNReal.toReal_ofReal hb0.le] at this
  have hgup : ∀ ω, g ω ≤ 1 := by
    intro ω
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hup ω)
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hb0 (hglow ω)
  have hreal := lemma_alpha_real μ q hq α hα g hg hglow hgup
  have hint_g : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hgpos ω, hgup ω]
  have hbound : ∀ ω, g ω ^ (-α) ≤ aConst q α := by
    intro ω
    calc g ω ^ (-α) ≤ (aConst q α ^ (-(1 / α))) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hb0 (hglow ω) (by linarith)
      _ = aConst q α := by
          rw [← Real.rpow_mul ha0.le]
          have : -(1 / α) * -α = 1 := by field_simp
          rw [this, Real.rpow_one]
  have hint_inv : Integrable (fun ω => g ω ^ (-α)) μ := by
    refine Integrable.of_bound (hg.pow_const (-α)).aestronglyMeasurable (aConst q α)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := Real.rpow_nonneg (hgpos ω).le (-α); linarith
    · exact hbound ω
  have e1 : ∫⁻ ω, h ω ∂μ = ENNReal.ofReal (∫ ω, g ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_g (Filter.Eventually.of_forall fun ω => (hgpos ω).le)]
    congr 1
    ext ω
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  have e2 : ∫⁻ ω, (h ω ^ α)⁻¹ ∂μ = ENNReal.ofReal (∫ ω, g ω ^ (-α) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_inv
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hgpos ω).le _)]
    congr 1
    ext ω
    rw [Real.rpow_neg (hgpos ω).le, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (hgpos ω) _),
      ← ENNReal.ofReal_rpow_of_pos (hgpos ω)]
    simp [hg_def, ENNReal.ofReal_toReal (hne ω)]
  have hu0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg fun ω => (hgpos ω).le
  rw [e1, e2, ENNReal.ofReal_rpow_of_nonneg hu0 hα0,
    ← ENNReal.ofReal_pow (Real.rpow_nonneg hu0 α),
    ← ENNReal.ofReal_mul (integral_nonneg fun ω => Real.rpow_nonneg (hgpos ω).le _),
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hreal

theorem corollary_alpha {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (ENNReal.ofReal (aConst q α)) ((g i ω) ^ α)⁻¹ ∂μ) ≤
      (∏ i : Fin q, (∫⁻ ω, g i ω ∂μ) ^ α)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  have ha1 : 1 < aConst q α := (aConst_facts q hq α hα).1
  have ha0 : 0 < aConst q α := by linarith
  have hb0 : 0 < aConst q α ^ (-(1 / α)) := Real.rpow_pos_of_pos ha0 _
  have hα0 : 0 ≤ α := by linarith
  have hα0' : α ≠ 0 := by positivity
  set b' : ℝ≥0∞ := ENNReal.ofReal (aConst q α ^ (-(1 / α))) with hb'
  set h : Ω → ℝ≥0∞ := fun ω => max b' (⨆ i, g i ω) with hh_def
  have hh : Measurable h := measurable_const.max (Measurable.iSup hg)
  have hlow : ∀ ω, b' ≤ h ω := fun ω => le_max_left _ _
  have hb1 : b' ≤ 1 := by
    rw [hb', ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos ha1.le (by
      have : 0 < 1 / α := by positivity
      linarith))
  have hup' : ∀ ω, h ω ≤ 1 := fun ω => max_le hb1 (iSup_le fun i => hup i ω)
  have hbinv : (b' ^ α)⁻¹ = ENNReal.ofReal (aConst q α) := by
    rw [hb', ENNReal.ofReal_rpow_of_pos hb0, ← Real.rpow_mul ha0.le]
    have : -(1 / α) * α = -1 := by field_simp
    rw [this, Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ha0, inv_inv]
  have hle : ∀ ω, (⨅ i : Fin q, min (ENNReal.ofReal (aConst q α)) ((g i ω) ^ α)⁻¹) ≤
      (h ω ^ α)⁻¹ := by
    intro ω
    by_cases hc : (⨆ i, g i ω) ≤ b'
    · have : h ω = b' := max_eq_left hc
      rw [this, hbinv]
      exact le_trans (iInf_le _ (Classical.arbitrary _)) (min_le_left _ _)
    · push Not at hc
      have : h ω = ⨆ i, g i ω := max_eq_right hc.le
      rw [this]
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => g i ω)
      rw [← hi]
      exact le_trans (iInf_le _ i) (min_le_right _ _)
  have hgh : ∀ i ω, g i ω ≤ h ω := fun i ω =>
    le_trans (le_iSup (fun i => g i ω) i) (le_max_right _ _)
  calc (∫⁻ ω, ⨅ i : Fin q, min (ENNReal.ofReal (aConst q α)) ((g i ω) ^ α)⁻¹ ∂μ) *
        ∏ i : Fin q, (∫⁻ ω, g i ω ∂μ) ^ α
      ≤ (∫⁻ ω, (h ω ^ α)⁻¹ ∂μ) * ∏ i : Fin q, (∫⁻ ω, h ω ∂μ) ^ α := by
        refine mul_le_mul' (lintegral_mono hle) ?_
        exact Finset.prod_le_prod' fun i _ =>
          ENNReal.rpow_le_rpow (lintegral_mono fun ω => hgh i ω) hα0
    _ = (∫⁻ ω, (h ω ^ α)⁻¹ ∂μ) * ((∫⁻ ω, h ω ∂μ) ^ α) ^ q := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 1 := lemma_alpha_ennreal μ q hq α hα h hh hlow hup'

/-! ### `epow` lemmas -/

lemma epow_coe (a : ℝ≥0∞) (m : ℕ) : epow a (m : ℕ∞) = a ^ m := by
  simp [epow]

lemma epow_top' (a : ℝ≥0∞) : epow a ⊤ = ⊤ := by
  simp [epow]

lemma epow_mono {a : ℝ≥0∞} (ha : 1 ≤ a) {m n : ℕ∞} (h : m ≤ n) : epow a m ≤ epow a n := by
  induction n using ENat.recTopCoe with
  | top => rw [epow_top']; exact le_top
  | coe n =>
    induction m using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe m =>
      rw [epow_coe, epow_coe]
      exact pow_le_pow_right₀ ha (by exact_mod_cast h)

lemma epow_one_add (a : ℝ≥0∞) (ha : a ≠ 0) (n : ℕ∞) : epow a (1 + n) = a * epow a n := by
  induction n using ENat.recTopCoe with
  | top => simp [epow, ENNReal.mul_top ha]
  | coe n =>
    have : (1 : ℕ∞) + n = ((1 + n : ℕ) : ℕ∞) := by push_cast; rfl
    rw [this, epow_coe, epow_coe, pow_add, pow_one]

/-! ### Choice of a good measurable sub-projection -/

lemma exists_good_proj {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (A : Set (Fin (N + 1) → Ω)) (hsl : ∀ ω, MeasurableSet (sliceAt A ω)) :
    ∃ B : Set (Fin N → Ω), MeasurableSet B ∧ B ⊆ projLast A ∧
      ∀ ω, (Measure.pi fun _ : Fin N => μ) (sliceAt A ω) ≤ (Measure.pi fun _ : Fin N => μ) B := by
  haveI : Nonempty Ω := Measure.nonempty_of_neZero μ
  set P := Measure.pi fun _ : Fin N => μ with hP
  set S := Set.range (fun ω => P (sliceAt A ω)) with hS
  obtain ⟨u, -, hlim, hmem⟩ :=
    exists_seq_tendsto_sSup (S := S) (Set.range_nonempty _) (OrderTop.bddAbove S)
  choose ω' hω' using hmem
  refine ⟨⋃ n, sliceAt A (ω' n), MeasurableSet.iUnion fun n => hsl _, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact ⟨ω' n, hn⟩
  · intro ω
    calc P (sliceAt A ω) ≤ sSup S := le_csSup (OrderTop.bddAbove S) ⟨ω, rfl⟩
      _ ≤ P (⋃ n, sliceAt A (ω' n)) := by
        refine le_of_tendsto' hlim fun n => ?_
        rw [← hω' n]
        exact measure_mono (Set.subset_iUnion (fun n => sliceAt A (ω' n)) n)


/-- The general induction with base `a` and exponent `α`, given the corollary-type bound. -/
theorem main_induction_gen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (a : ℝ≥0∞) (ha1 : 1 ≤ a) (hatop : a ≠ ⊤) (α : ℝ) (hα : 0 < α)
    (Hcor : ∀ g : Fin q → Ω → ℝ≥0∞, (∀ i, Measurable (g i)) → (∀ i ω, g i ω ≤ 1) →
      (∫⁻ ω, ⨅ j : Fin q, min a ((g j ω) ^ α)⁻¹ ∂μ) ≤ (∏ j : Fin q, (∫⁻ ω, g j ω ∂μ) ^ α)⁻¹) :
    ∀ (N : ℕ) (A : Fin q → Set (Fin N → Ω)), (∀ i, MeasurableSet (A i)) →
      ∫⁻ x, epow a (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
        (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i) ^ α)⁻¹ := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha1; exact absurd ha1 (by simp)
  have hα0 : 0 ≤ α := hα.le
  intro N
  induction N with
  | zero =>
    intro A hA
    by_cases hne : ∀ i, (A i).Nonempty
    · choose y hy using hne
      have h0 : ∀ x, qDist A x = 0 := by
        intro x
        apply le_antisymm _ zero_le
        refine le_trans (qDist_le_of_mem A x y hy) ?_
        simp [uncaptured]
      simp only [h0]
      have h1 : epow a 0 = 1 := by
        rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, epow_coe, pow_zero]
      rw [h1, lintegral_const, measure_univ, mul_one, ENNReal.le_inv_iff_mul_le, one_mul]
      exact Finset.prod_le_one (fun i _ => zero_le) (fun i _ => ENNReal.rpow_le_one prob_le_one hα0)
    · push Not at hne
      obtain ⟨i, hi⟩ := hne
      have : ∏ j, (Measure.pi fun _ : Fin 0 => μ) (A j) ^ α = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, ENNReal.zero_rpow_of_pos hα])
      rw [this, ENNReal.inv_zero]
      exact le_top
  | succ N ih =>
    intro A hA
    set P : Measure (Fin N → Ω) := Measure.pi fun _ : Fin N => μ with hP
    set P' : Measure (Fin (N + 1) → Ω) := Measure.pi fun _ : Fin (N + 1) => μ with hP'
    let e : (Fin (N + 1) → Ω) ≃ᵐ Ω × (Fin N → Ω) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => Ω) (Fin.last N)
    have hmp : MeasurePreserving e P' (μ.prod P) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) (Fin.last N)
    have he : ∀ (ω : Ω) (x : Fin N → Ω), e.symm (ω, x) = (Fin.snoc x ω : Fin (N + 1) → Ω) := by
      intro ω x
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    have hslice : ∀ i ω, sliceAt (A i) ω = Prod.mk ω ⁻¹' (e.symm ⁻¹' A i) := by
      intro i ω
      ext x
      simp [sliceAt, he]
    have hslice_meas : ∀ i ω, MeasurableSet (sliceAt (A i) ω) := by
      intro i ω
      rw [hslice]
      exact measurable_prodMk_left (e.symm.measurable (hA i))
    have hmeas_slice : ∀ i, Measurable (fun ω => P (sliceAt (A i) ω)) := by
      intro i
      simp_rw [hslice]
      exact measurable_measure_prodMk_left (e.symm.measurable (hA i))
    have hfub : ∀ i, ∫⁻ ω, P (sliceAt (A i) ω) ∂μ = P' (A i) := by
      intro i
      rw [← (hmp.symm e).measure_preimage (hA i).nullMeasurableSet,
        Measure.prod_apply (e.symm.measurable (hA i))]
      simp_rw [hslice]
    have htrans : ∫⁻ z, epow a (qDist A z) ∂P' ≤
        ∫⁻ ω, ∫⁻ x, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ∂μ := by
      calc ∫⁻ z, epow a (qDist A z) ∂P'
          = ∫⁻ p, epow a (qDist A (e.symm p)) ∂(μ.prod P) :=
            ((hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding _).symm
        _ ≤ ∫⁻ ω, ∫⁻ x, epow a (qDist A (e.symm (ω, x))) ∂P ∂μ := lintegral_prod_le _
        _ = _ := by simp_rw [he]
    by_cases hz : ∃ i, P' (A i) = 0
    · obtain ⟨i, hi⟩ := hz
      have : ∏ j, P' (A j) ^ α = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, ENNReal.zero_rpow_of_pos hα])
      rw [this, ENNReal.inv_zero]
      exact le_top
    push Not at hz
    choose B hBm hBsub hBle using fun i => exists_good_proj μ (A i) (hslice_meas i)
    have hPAle : ∀ i, P' (A i) ≤ P (B i) := by
      intro i
      rw [← hfub i]
      calc ∫⁻ ω, P (sliceAt (A i) ω) ∂μ ≤ ∫⁻ ω, P (B i) ∂μ := lintegral_mono fun ω => hBle i ω
        _ = P (B i) := by rw [lintegral_const, measure_univ, mul_one]
    have hB0 : ∀ i, P (B i) ≠ 0 := fun i h => hz i (le_antisymm (h ▸ hPAle i) zero_le)
    have hBtop : ∀ i, P (B i) ≠ ⊤ := fun i => measure_ne_top _ _
    have hBα0 : ∀ i, P (B i) ^ α ≠ 0 := fun i =>
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hB0 i)) (hBtop i)).ne'
    have hBαtop : ∀ i, P (B i) ^ α ≠ ⊤ := fun i => ENNReal.rpow_ne_top_of_nonneg hα0 (hBtop i)
    set PB := ∏ i, P (B i) ^ α with hPB
    have hPB0 : PB ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hBα0 i
    have hPBtop : PB ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hBαtop i
    let C : Fin q → Ω → Fin q → Set (Fin N → Ω) := fun j ω => Function.update B j (sliceAt (A j) ω)
    have hCm : ∀ j ω i, MeasurableSet (C j ω i) := by
      intro j ω i
      by_cases h : i = j
      · subst h; simp [C, hslice_meas]
      · simp only [C, Function.update_of_ne h]; exact hBm i
    have hb1 : ∀ x ω, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ≤
        a * epow a (qDist B x) := by
      intro x ω
      have h1 := (eq_3_1_6_core hq A x ω).1
      have h2 := qDist_anti B (fun i => projLast (A i)) x hBsub
      calc epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω))
          ≤ epow a (1 + qDist B x) :=
            epow_mono ha1 (le_trans h1 (add_le_add le_rfl h2))
        _ = a * epow a (qDist B x) := epow_one_add _ ha0 _
    have hb2 : ∀ x ω j, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ≤
        epow a (qDist (C j ω) x) := by
      intro x ω j
      have h1 := (eq_3_1_6_core hq A x ω).2 j
      have h2 : qDist (Function.update (fun i => projLast (A i)) j (sliceAt (A j) ω)) x ≤
          qDist (C j ω) x := by
        apply qDist_anti
        intro i
        by_cases h : i = j
        · subst h; simp [C]
        · simp only [C, Function.update_of_ne h]; exact hBsub i
      exact epow_mono ha1 (le_trans h1 h2)
    let g : Fin q → Ω → ℝ≥0∞ := fun j ω => P (sliceAt (A j) ω) * (P (B j))⁻¹
    have hg_meas : ∀ j, Measurable (g j) := fun j => (hmeas_slice j).mul_const _
    have hg_le : ∀ j ω, g j ω ≤ 1 := by
      intro j ω
      calc g j ω = P (sliceAt (A j) ω) * (P (B j))⁻¹ := rfl
        _ ≤ P (B j) * (P (B j))⁻¹ := mul_le_mul' (hBle j ω) le_rfl
        _ = 1 := ENNReal.mul_inv_cancel (hB0 j) (hBtop j)
    have hg_int : ∀ j, (∫⁻ ω, g j ω ∂μ) ^ α = P' (A j) ^ α * (P (B j) ^ α)⁻¹ := by
      intro j
      simp only [g]
      rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hB0 j)), hfub,
        ENNReal.mul_rpow_of_nonneg _ _ hα0, ENNReal.inv_rpow]
    have J : ∀ ω, ∫⁻ x, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ≤
        PB⁻¹ * ⨅ j, min a ((g j ω) ^ α)⁻¹ := by
      intro ω
      set X := ∫⁻ x, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P with hX
      have I1 : X ≤ a * PB⁻¹ := by
        calc X ≤ ∫⁻ x, a * epow a (qDist B x) ∂P := lintegral_mono fun x => hb1 x ω
          _ = a * ∫⁻ x, epow a (qDist B x) ∂P := lintegral_const_mul' _ _ hatop
          _ ≤ a * PB⁻¹ := by gcongr; exact ih B hBm
      have I2 : ∀ j, X ≤ (∏ i, P (C j ω i) ^ α)⁻¹ := by
        intro j
        calc X ≤ ∫⁻ x, epow a (qDist (C j ω) x) ∂P := lintegral_mono fun x => hb2 x ω j
          _ ≤ _ := ih (C j ω) (hCm j ω)
      rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hPB0) (Or.inl hPBtop)]
      refine le_iInf fun j => le_min ?_ ?_
      · calc X * PB ≤ a * PB⁻¹ * PB := by gcongr
          _ = a := by rw [mul_assoc, ENNReal.inv_mul_cancel hPB0 hPBtop, mul_one]
      · set R := ∏ i ∈ Finset.univ.erase j, P (B i) ^ α with hR
        have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hBα0 i
        have hRtop : R ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hBαtop i
        have hPBeq : PB = P (B j) ^ α * R :=
          (Finset.mul_prod_erase Finset.univ (fun i => P (B i) ^ α) (Finset.mem_univ j)).symm
        have hCeq : ∏ i, P (C j ω i) ^ α = P (sliceAt (A j) ω) ^ α * R := by
          calc ∏ i, P (C j ω i) ^ α
              = P (C j ω j) ^ α * ∏ i ∈ Finset.univ.erase j, P (C j ω i) ^ α :=
                (Finset.mul_prod_erase Finset.univ (fun i => P (C j ω i) ^ α)
                  (Finset.mem_univ j)).symm
            _ = P (sliceAt (A j) ω) ^ α * R := by
                congr 1
                · simp [C]
                · exact Finset.prod_congr rfl fun i hi => by
                    simp [C, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        have hS_top : P (sliceAt (A j) ω) ^ α ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg hα0 (measure_ne_top _ _)
        have hginv : ((g j ω) ^ α)⁻¹ = (P (sliceAt (A j) ω) ^ α)⁻¹ * P (B j) ^ α := by
          simp only [g]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα0, ENNReal.inv_rpow,
            ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 (hBα0 j))) (Or.inl hS_top), inv_inv]
        rw [hginv, hPBeq]
        have I2' := I2 j
        rw [hCeq, ENNReal.mul_inv (Or.inr hRtop) (Or.inl hS_top)] at I2'
        calc X * (P (B j) ^ α * R)
            ≤ (P (sliceAt (A j) ω) ^ α)⁻¹ * R⁻¹ * (P (B j) ^ α * R) := by gcongr
          _ = (P (sliceAt (A j) ω) ^ α)⁻¹ * P (B j) ^ α * (R⁻¹ * R) := by ring
          _ = (P (sliceAt (A j) ω) ^ α)⁻¹ * P (B j) ^ α := by
              rw [ENNReal.inv_mul_cancel hR0 hRtop, mul_one]
    have hQ0 : ∏ j, P' (A j) ^ α ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ =>
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hz j)) (measure_ne_top _ _)).ne'
    have hQtop : ∏ j, P' (A j) ^ α ≠ ⊤ := ENNReal.prod_ne_top fun j _ =>
      ENNReal.rpow_ne_top_of_nonneg hα0 (measure_ne_top _ _)
    calc ∫⁻ z, epow a (qDist A z) ∂P'
        ≤ ∫⁻ ω, ∫⁻ x, epow a (qDist A (Fin.snoc x ω : Fin (N + 1) → Ω)) ∂P ∂μ := htrans
      _ ≤ ∫⁻ ω, PB⁻¹ * ⨅ j, min a ((g j ω) ^ α)⁻¹ ∂μ := lintegral_mono J
      _ = PB⁻¹ * ∫⁻ ω, ⨅ j, min a ((g j ω) ^ α)⁻¹ ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hPB0)
      _ ≤ PB⁻¹ * (∏ j, (∫⁻ ω, g j ω ∂μ) ^ α)⁻¹ := by
          gcongr; exact Hcor g hg_meas hg_le
      _ = PB⁻¹ * ((∏ j, P' (A j) ^ α) * PB⁻¹)⁻¹ := by
          simp_rw [hg_int]
          rw [Finset.prod_mul_distrib, hPB,
            ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (hBα0 i))]
      _ = (∏ j, P' (A j) ^ α)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl hQ0) (Or.inl hQtop), inv_inv]
          calc PB⁻¹ * ((∏ j, P' (A j) ^ α)⁻¹ * PB) = (∏ j, P' (A j) ^ α)⁻¹ * (PB⁻¹ * PB) := by ring
            _ = _ := by rw [ENNReal.inv_mul_cancel hPB0 hPBtop, mul_one]

theorem eq_3_2_1_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (A : Fin q → Set (Fin N → Ω))
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫⁻ x, epow (ENNReal.ofReal (aConst q α)) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i) ^ α)⁻¹ := by
  have ha1 : 1 < aConst q α := (aConst_facts q hq α hα).1
  exact main_induction_gen μ q hq (ENNReal.ofReal (aConst q α))
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ha1.le) ENNReal.ofReal_ne_top
    α (by linarith) (corollary_alpha μ q hq α hα) N A hA

end TalagrandConc.QPoints

open TalagrandConc.QPoints
open MeasureTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (A : Fin q → Set (Fin N → Ω))
    (hA : ∀ i, MeasurableSet (A i)) (hf : Measurable (qDist A)) :
    ∫⁻ x, epow (ENNReal.ofReal (aConst q α)) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i) ^ α)⁻¹ := by
  exact eq_3_2_1_core μ N q hq α hα A hA
