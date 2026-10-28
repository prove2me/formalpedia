-- Prove2me | solution 1 for RefMNLPricing.Myopic.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:30:24.321628+00:00
-- url     : https://prove2.me/submissions/8f8400a4-7736-4d86-94fd-641fbbcb0aa7

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13
import Theorems.Thm_RefMNLPricing_Myopic_theorem_2
import Theorems.Thm_RefMNLPricing_Myopic_theorem_3_convergence

open Filter Topology RefMNLPricing.Myopic

namespace RefMNLT3Aux

/-- Joint continuity of the single-period revenue in `(p, r)`. -/
lemma revenue_continuous {n : ℕ} (a b cp cm : Fin n → ℝ) :
    Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) => revenue a b cp cm x.1 x.2) := by
  have hu : ∀ i, Continuous
      (fun x : (Fin n → ℝ) × (Fin n → ℝ) => util a b cp cm x.1 x.2 i) := by
    intro i
    unfold util
    fun_prop
  unfold revenue share
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine ((continuous_apply i).comp continuous_fst).mul ?_
  refine ((hu i).rexp).div
    (continuous_const.add (continuous_finset_sum _ fun k _ => (hu k).rexp)) ?_
  intro x
  have : 0 ≤ ∑ k, Real.exp (util a b cp cm x.1 x.2 k) :=
    Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  linarith

/-- Linear recursion `e_{t+1} = α e_t + (1-α) d_t` with `d → 0`, `0 ≤ α < 1` forces `e → 0`. -/
lemma tendsto_of_recursion (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (e d : ℕ → ℝ)
    (hrec : ∀ t, e (t + 1) = α * e t + (1 - α) * d t)
    (hd : Tendsto d atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hd ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hd (ε / 2) (by positivity)
  have key : ∀ k, |e (N + k)| ≤ α ^ k * |e N| + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hdk := hN (N + k) (by omega)
      rw [Real.dist_eq, sub_zero] at hdk
      rw [show N + (k + 1) = (N + k) + 1 by ring, hrec]
      have h1' : 0 ≤ 1 - α := by linarith
      calc |α * e (N + k) + (1 - α) * d (N + k)|
          ≤ |α * e (N + k)| + |(1 - α) * d (N + k)| := abs_add_le _ _
        _ = α * |e (N + k)| + (1 - α) * |d (N + k)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1']
        _ ≤ α * (α ^ k * |e N| + ε / 2) + (1 - α) * (ε / 2) := by
          have := mul_le_mul_of_nonneg_left ih h0
          have := mul_le_mul_of_nonneg_left hdk.le h1'
          linarith
        _ = α ^ (k + 1) * |e N| + ε / 2 := by ring
  have hpow : Tendsto (fun k : ℕ => α ^ k * |e N|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (|e N|)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hpow) (ε / 2) (by positivity)
  refine ⟨N + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = N + k := ⟨t - N, by omega⟩
  have hk := hK k (by omega)
  rw [Real.dist_eq, sub_zero] at hk
  rw [Real.dist_eq, sub_zero]
  have hk' := key k
  have : α ^ k * |e N| < ε / 2 := lt_of_abs_lt hk
  linarith

/-- The box `Pⁿ` is closed. -/
lemma inBox_of_tendsto {n : ℕ} (pH : ℝ) (pp : ℕ → Fin n → ℝ) (L : Fin n → ℝ)
    (hbox : ∀ t, InBox pH (pp t)) (hp : Tendsto pp atTop (𝓝 L)) : InBox pH L := by
  intro i
  have hi : Tendsto (fun t => pp t i) atTop (𝓝 (L i)) := tendsto_pi_nhds.1 hp i
  exact isClosed_Icc.mem_of_tendsto hi (Eventually.of_forall fun t => hbox t i)

/-- Closed graph of the argmax correspondence (Berge). -/
lemma closed_graph {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) (rr pp : ℕ → Fin n → ℝ)
    (R L : Fin n → ℝ) (hr : Tendsto rr atTop (𝓝 R)) (hp : Tendsto pp atTop (𝓝 L))
    (hmax : ∀ t, IsBoxMax a b cp cm pH (rr t) (pp t)) : IsBoxMax a b cp cm pH R L := by
  refine ⟨inBox_of_tendsto pH pp L (fun t => (hmax t).1) hp, fun p' hp' => ?_⟩
  have hc := revenue_continuous a b cp cm
  have h1 : Tendsto (fun t => revenue a b cp cm p' (rr t)) atTop
      (𝓝 (revenue a b cp cm p' R)) :=
    (hc.tendsto (p', R)).comp (tendsto_const_nhds.prodMk_nhds hr)
  have h2 : Tendsto (fun t => revenue a b cp cm (pp t) (rr t)) atTop
      (𝓝 (revenue a b cp cm L R)) :=
    (hc.tendsto (L, R)).comp (hp.prodMk_nhds hr)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun t => (hmax t).2 p' hp')

/-- Strict bounds `1/y < (log y - log x)/(y - x) < 1/x` for `0 < x < y`. -/
lemma log_slope_bounds (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    1 / y < (Real.log y - Real.log x) / (y - x) ∧
      (Real.log y - Real.log x) / (y - x) < 1 / x := by
  have hy : 0 < y := lt_trans hx hxy
  have hyx : 0 < y - x := by linarith
  have hA : Real.log y - Real.log x < (y - x) / x := by
    have h := Real.log_lt_sub_one_of_pos (div_pos hy hx) (by
      intro h; rw [div_eq_one_iff_eq hx.ne'] at h; linarith)
    rw [Real.log_div hy.ne' hx.ne'] at h
    have : y / x - 1 = (y - x) / x := by field_simp
    linarith
  have hB : (y - x) / y < Real.log y - Real.log x := by
    have h := Real.log_lt_sub_one_of_pos (div_pos hx hy) (by
      intro h; rw [div_eq_one_iff_eq hy.ne'] at h; linarith)
    rw [Real.log_div hx.ne' hy.ne'] at h
    have : x / y - 1 = -((y - x) / y) := by field_simp; ring
    linarith
  constructor
  · rw [div_lt_div_iff₀ hy hyx]
    have := (div_lt_iff₀ hy).1 hB
    linarith
  · rw [div_lt_div_iff₀ hyx hx]
    have := (lt_div_iff₀ hx).1 hA
    linarith

/-- With a gain-seeking product, no `r ∈ Pⁿ` is a maximiser of `Π(·, r)`. -/
lemma no_fixed_max {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH) (r : Fin n → ℝ) (hr : InBox pH r)
    (hmax : IsBoxMax a b cp cm pH r r) (i : Fin n) (hi : cm i < cp i) : False := by
  obtain ⟨_, _, h3⟩ := theorem_2 a b cp cm pH hb hcp hcm hpH hceil r r hr hmax i
  obtain ⟨_, hlt, hgt, heq⟩ := h3 hi
  have hx : 0 < b i + cm i := by linarith [hb i, hcm i]
  have hZ := log_slope_bounds (b i + cm i) (b i + cp i) hx (by linarith)
  have hZdef : Zgap b cp cm i =
      (Real.log (b i + cp i) - Real.log (b i + cm i)) / ((b i + cp i) - (b i + cm i)) := by
    unfold Zgap; congr 1; ring
  rw [← hZdef] at hZ
  obtain ⟨hZ1, hZ2⟩ := hZ
  rcases lt_trichotomy (r i) (revenue a b cp cm r r + Zgap b cp cm i) with h | h | h
  · have := hlt h; linarith
  · rcases heq h with h' | h' <;> linarith
  · have := hgt h; linarith

/-- Without gain-seeking products, the maximiser of `Π(·, r)` over `Pⁿ` is unique. -/
lemma max_unique {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH) (hng : ∀ i, cp i ≤ cm i)
    (r p q : Fin n → ℝ) (hr : InBox pH r)
    (hp : IsBoxMax a b cp cm pH r p) (hq : IsBoxMax a b cp cm pH r q) : p = q := by
  have hv : revenue a b cp cm q r = revenue a b cp cm p r :=
    le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
  funext i
  obtain ⟨hp1, hp2, _⟩ := theorem_2 a b cp cm pH hb hcp hcm hpH hceil r p hr hp i
  obtain ⟨hq1, hq2, _⟩ := theorem_2 a b cp cm pH hb hcp hcm hpH hceil r q hr hq i
  rw [hv] at hq1 hq2
  rcases lt_or_eq_of_le (hng i) with hlt | heq
  · obtain ⟨pa, pb, pc⟩ := hp1 hlt
    obtain ⟨qa, qb, qc⟩ := hq1 hlt
    by_cases h1 : r i < revenue a b cp cm p r + 1 / (b i + cm i)
    · rw [pa h1, qa h1]
    · by_cases h2 : revenue a b cp cm p r + 1 / (b i + cp i) < r i
      · rw [pb h2, qb h2]
      · push_neg at h1 h2
        rw [pc h1 h2, qc h1 h2]
  · rw [hp2 heq, hq2 heq]

lemma ref_inBox {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (r₀ : Fin n → ℝ) (hr₀ : InBox pH r₀) : ∀ t, InBox pH (myopicRef pm α r₀ t) := by
  intro t
  induction t with
  | zero => exact hr₀
  | succ t ih =>
    intro i
    have hpi := (hpm _ ih).1 i
    have hri := ih i
    show α * myopicRef pm α r₀ t i + (1 - α) * pm (myopicRef pm α r₀ t) i ∈ Set.Icc 0 pH
    obtain ⟨h0, h1⟩ := hα
    obtain ⟨a1, a2⟩ := hri
    obtain ⟨b1, b2⟩ := hpi
    constructor <;> nlinarith

lemma ref_tendsto {n : ℕ} (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (h1 : α < 1)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (r₀ L : Fin n → ℝ)
    (hL : Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L)) :
    Tendsto (myopicRef pm α r₀) atTop (𝓝 L) := by
  rw [tendsto_pi_nhds] at hL ⊢
  intro i
  have hd : Tendsto (fun t => pm (myopicRef pm α r₀ t) i - L i) atTop (𝓝 0) := by
    simpa using (hL i).sub_const (L i)
  have := tendsto_of_recursion α hα.1 h1 (fun t => myopicRef pm α r₀ t i - L i)
    (fun t => pm (myopicRef pm α r₀ t) i - L i)
    (by intro t; show α * myopicRef pm α r₀ t i + (1 - α) * pm (myopicRef pm α r₀ t) i - L i = _
        ring) hd
  simpa using this.add_const (L i)

end RefMNLT3Aux

open RefMNLT3Aux in
theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm) :
    ((∀ i, cp i ≤ cm i) →
      ∀ r₀ : Fin n → ℝ, InBox pH r₀ →
        ∃ L : Fin n → ℝ, InBox pH L ∧
          Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L) ∧
          (α < 1 → pm L = L)) ∧
    ((∃ i, cm i < cp i) →
      (∀ r : Fin n → ℝ, InBox pH r → pm r ≠ r) ∧
      (α < 1 → ∀ r₀ : Fin n → ℝ, InBox pH r₀ →
        ¬ ∃ L : Fin n → ℝ, Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L))) := by
  have hmaxt : ∀ r₀, InBox pH r₀ → ∀ t,
      IsBoxMax a b cp cm pH (myopicRef pm α r₀ t) (pm (myopicRef pm α r₀ t)) :=
    fun r₀ hr₀ t => hpm _ (ref_inBox a b cp cm α pH hα pm hpm r₀ hr₀ t)
  constructor
  · intro hng r₀ hr₀
    obtain ⟨L, hL⟩ := theorem_3_convergence a b cp cm α pH hb hcp hcm hα hpH hceil pm hpm
      hng r₀ hr₀
    have hLbox : InBox pH L :=
      inBox_of_tendsto pH _ L (fun t => (hmaxt r₀ hr₀ t).1) hL
    refine ⟨L, hLbox, hL, fun h1 => ?_⟩
    have hR := ref_tendsto α hα h1 pm r₀ L hL
    have hLL : IsBoxMax a b cp cm pH L L := closed_graph a b cp cm pH _ _ L L hR hL (hmaxt r₀ hr₀)
    exact max_unique a b cp cm pH hb hcp hcm hpH hceil hng L (pm L) L hLbox (hpm L hLbox) hLL
  · rintro ⟨i, hi⟩
    refine ⟨fun r hr hfix => ?_, fun h1 r₀ hr₀ ⟨L, hL⟩ => ?_⟩
    · have hm := hpm r hr
      rw [hfix] at hm
      exact no_fixed_max a b cp cm pH hb hcp hcm hpH hceil r hr hm i hi
    · have hR := ref_tendsto α hα h1 pm r₀ L hL
      have hLL := closed_graph a b cp cm pH _ _ L L hR hL (hmaxt r₀ hr₀)
      exact no_fixed_max a b cp cm pH hb hcp hcm hpH hceil L hLL.1 hLL i hi
