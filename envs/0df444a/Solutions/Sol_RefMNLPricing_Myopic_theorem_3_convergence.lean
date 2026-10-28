-- Prove2me | solution 1 for RefMNLPricing.Myopic.theorem_3_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:50:33.057882+00:00
-- url     : https://prove2.me/submissions/86596fa1-3898-4811-a12c-19cce8177138

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Theorems.Thm_RefMNLPricing_Myopic_theorem_2
import Theorems.Thm_RefMNLPricing_Myopic_revenue_monotone

open Filter Topology RefMNLPricing.Myopic

namespace RefMNLT3ConvAux

variable {n : ℕ}

/-- Without gain-seeking products the myopic price is the clamp
`p_i = max (Π^m + 1/(b_i+c_i⁻)) (min r_i (Π^m + 1/(b_i+c_i⁺)))` (Theorem 2). -/
lemma formula (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH) (hng : ∀ i, cp i ≤ cm i)
    (r p : Fin n → ℝ) (hr : InBox pH r) (hp : IsBoxMax a b cp cm pH r p) (i : Fin n) :
    p i = max (revenue a b cp cm p r + 1 / (b i + cm i))
      (min (r i) (revenue a b cp cm p r + 1 / (b i + cp i))) := by
  obtain ⟨h1, h2, _⟩ := theorem_2 a b cp cm pH hb hcp hcm hpH hceil r p hr hp i
  set v := revenue a b cp cm p r
  have hlh : 1 / (b i + cm i) ≤ 1 / (b i + cp i) :=
    one_div_le_one_div_of_le (by linarith [hb i, hcp i]) (by linarith [hng i])
  rcases lt_or_eq_of_le (hng i) with hc | hc
  · obtain ⟨a1, a2, a3⟩ := h1 hc
    by_cases e1 : r i < v + 1 / (b i + cm i)
    · rw [a1 e1, min_eq_left (by linarith), max_eq_left e1.le]
    · by_cases e2 : v + 1 / (b i + cp i) < r i
      · rw [a2 e2, min_eq_right e2.le, max_eq_right (by linarith)]
      · push_neg at e1 e2
        rw [a3 e1 e2, min_eq_left e2, max_eq_right e1]
  · rw [h2 hc, ← hc, min_le_iff.mpr (Or.inr le_rfl) |> fun h => max_eq_left h]

lemma ref_inBox (a b cp cm : Fin n → ℝ) (α pH : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
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

/-- Monotone convergence in `ℝⁿ` for a monotone bounded sequence. -/
lemma conv_of_monotone (f : ℕ → Fin n → ℝ) (pH : ℝ) (hf : Monotone f)
    (hb : ∀ k i, f k i ≤ pH) : ∃ L, Tendsto f atTop (𝓝 L) := by
  refine ⟨fun i => ⨆ k, f k i, tendsto_pi_nhds.2 (fun i => ?_)⟩
  exact tendsto_atTop_ciSup (fun k l hkl => hf hkl i) ⟨pH, by rintro _ ⟨k, rfl⟩; exact hb k i⟩

lemma conv_of_antitone (f : ℕ → Fin n → ℝ) (hf : Antitone f)
    (hb : ∀ k i, 0 ≤ f k i) : ∃ L, Tendsto f atTop (𝓝 L) := by
  refine ⟨fun i => ⨅ k, f k i, tendsto_pi_nhds.2 (fun i => ?_)⟩
  exact tendsto_atTop_ciInf (fun k l hkl => hf hkl i) ⟨0, by rintro _ ⟨k, rfl⟩; exact hb k i⟩

lemma shift_conv (f : ℕ → Fin n → ℝ) (t0 : ℕ) (h : ∃ L, Tendsto (fun k => f (t0 + k)) atTop (𝓝 L)) :
    ∃ L, Tendsto f atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, (Filter.tendsto_add_atTop_iff_nat t0).1 ?_⟩
  simpa [add_comm] using hL

end RefMNLT3ConvAux

open RefMNLT3ConvAux in
theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ) (α pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hpH : 0 < pH) (hceil : CeilingOK a b cp cm pH)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (hpm : IsMyopicSel a b cp cm pH pm)
    (hng : ∀ i, cp i ≤ cm i) (r₀ : Fin n → ℝ) (hr₀ : InBox pH r₀) :
    ∃ L : Fin n → ℝ, Tendsto (fun t => pm (myopicRef pm α r₀ t)) atTop (𝓝 L) := by
  obtain ⟨hα0, hα1⟩ := hα
  set rr := myopicRef pm α r₀ with hrr
  have rbox : ∀ t, InBox pH (rr t) := ref_inBox a b cp cm α pH ⟨hα0, hα1⟩ pm hpm r₀ hr₀
  have hrec : ∀ t i, rr (t + 1) i = α * rr t i + (1 - α) * pm (rr t) i := fun t i => rfl
  -- α = 1: the reference price never moves
  rcases lt_or_eq_of_le hα1 with hlt1 | heq1
  swap
  · have hconst : ∀ t, rr t = r₀ := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => funext i; rw [hrec, ih, heq1]; ring
    exact ⟨pm r₀, by simp only [hconst]; exact tendsto_const_nhds⟩
  -- notation
  set lo : Fin n → ℝ := fun i => 1 / (b i + cm i) with hlo
  set hi : Fin n → ℝ := fun i => 1 / (b i + cp i) with hhi
  have hlohi : ∀ i, lo i ≤ hi i := fun i =>
    one_div_le_one_div_of_le (by linarith [hb i, hcp i]) (by linarith [hng i])
  set ss : ℕ → ℝ := fun t => revenue a b cp cm (pm (rr t)) (rr t) with hss
  have hform : ∀ t i, pm (rr t) i = max (ss t + lo i) (min (rr t i) (ss t + hi i)) :=
    fun t i => formula a b cp cm pH hb hcp hcm hpH hceil hng (rr t) (pm (rr t)) (rbox t)
      (hpm _ (rbox t)) i
  -- the myopic policy is monotone on the box
  have pmono : ∀ r r' : Fin n → ℝ, InBox pH r → InBox pH r' → r ≤ r' → pm r ≤ pm r' := by
    intro r r' hr hr' hle i
    have hs := revenue_monotone a b cp cm pH hb hcp hcm hpH hceil r r' (pm r) (pm r') hr hr'
      hle (hpm r hr) (hpm r' hr')
    rw [formula a b cp cm pH hb hcp hcm hpH hceil hng r (pm r) hr (hpm r hr) i,
      formula a b cp cm pH hb hcp hcm hpH hceil hng r' (pm r') hr' (hpm r' hr') i]
    exact max_le_max (by linarith) (min_le_min (hle i) (by linarith))
  -- monotone cases
  by_cases hmon : ∃ t0, (∀ i, rr t0 i ≤ pm (rr t0) i) ∨ (∀ i, pm (rr t0) i ≤ rr t0 i)
  · obtain ⟨t0, hup | hdown⟩ := hmon
    · have step : ∀ k, rr (t0 + k) ≤ rr (t0 + k + 1) := by
        intro k
        induction k with
        | zero =>
          intro i
          simp only [Nat.add_zero]
          rw [hrec]
          have := hup i
          nlinarith
        | succ k ih =>
          have hP := pmono _ _ (rbox _) (rbox _) ih
          intro i
          rw [show t0 + (k + 1) + 1 = (t0 + k + 1) + 1 by ring, hrec (t0 + k + 1),
            show t0 + (k + 1) = t0 + k + 1 by ring, hrec (t0 + k)]
          have := ih i
          have := hP i
          rw [hrec (t0 + k)] at *
          nlinarith
      apply shift_conv _ t0
      apply conv_of_monotone _ pH
      · exact monotone_nat_of_le_succ (fun k => pmono _ _ (rbox _) (rbox _) (step k))
      · intro k i; exact ((hpm _ (rbox _)).1 i).2
    · have step : ∀ k, rr (t0 + k + 1) ≤ rr (t0 + k) := by
        intro k
        induction k with
        | zero =>
          intro i
          simp only [Nat.add_zero]
          rw [hrec]
          have := hdown i
          nlinarith
        | succ k ih =>
          have hP := pmono _ _ (rbox _) (rbox _) ih
          intro i
          rw [show t0 + (k + 1) + 1 = (t0 + k + 1) + 1 by ring, hrec (t0 + k + 1),
            show t0 + (k + 1) = t0 + k + 1 by ring, hrec (t0 + k)]
          have := ih i
          have := hP i
          rw [hrec (t0 + k)] at *
          nlinarith
      apply shift_conv _ t0
      apply conv_of_antitone
      · exact antitone_nat_of_succ_le (fun k => pmono _ _ (rbox _) (rbox _) (step k))
      · intro k i; exact ((hpm _ (rbox _)).1 i).1
  -- the mixed case persists forever: geometric contraction
  push_neg at hmon
  have hA : ∀ t, ∃ i, ss t + hi i < rr t i := by
    intro t
    obtain ⟨⟨i, hi'⟩, _⟩ := hmon t
    refine ⟨i, ?_⟩
    by_contra h
    push_neg at h
    rw [hform t i, min_eq_left h] at hi'
    exact absurd (le_max_right _ _) (not_le.2 hi')
  have hB : ∀ t, ∃ j, rr t j < ss t + lo j := by
    intro t
    obtain ⟨_, ⟨j, hj'⟩⟩ := hmon t
    refine ⟨j, ?_⟩
    by_contra h
    push_neg at h
    rw [hform t j] at hj'
    have : max (ss t + lo j) (min (rr t j) (ss t + hi j)) ≤ rr t j :=
      max_le h (min_le_left _ _)
    linarith
  -- one-step bounds
  have up1 : ∀ t i, rr (t + 1) i - ss t - hi i ≤ α * max (rr t i - ss t - hi i) 0 := by
    intro t i
    rw [hrec, hform t i]
    have hl := hlohi i
    rcases le_or_gt (rr t i) (ss t + hi i) with h | h
    · rw [min_eq_left h]
      have : max (ss t + lo i) (rr t i) ≤ ss t + hi i := max_le (by linarith) h
      have := le_max_right (rr t i - ss t - hi i) 0
      nlinarith
    · rw [min_eq_right h.le, max_eq_right (by linarith), max_eq_left (by linarith)]
      ring_nf; nlinarith
  have dn1 : ∀ t j, ss t + lo j - rr (t + 1) j ≤ α * max (ss t + lo j - rr t j) 0 := by
    intro t j
    rw [hrec, hform t j]
    have hl := hlohi j
    rcases le_or_gt (ss t + lo j) (rr t j) with h | h
    · have : ss t + lo j ≤ max (ss t + lo j) (min (rr t j) (ss t + hi j)) := le_max_left _ _
      have := le_max_right (ss t + lo j - rr t j) 0
      nlinarith
    · rw [min_eq_left (by linarith), max_eq_left h.le, max_eq_left (by linarith)]
      ring_nf; nlinarith
  set K : ℝ := ∑ i, max (rr 0 i - ss 0 - hi i) 0 + ∑ j, max (ss 0 + lo j - rr 0 j) 0 with hK
  have hK0 : 0 ≤ K := add_nonneg (Finset.sum_nonneg (fun i _ => le_max_right _ _))
    (Finset.sum_nonneg (fun i _ => le_max_right _ _))
  have Q : ∀ t, ∀ i j, max (rr t i - ss t - hi i) 0 + max (ss t + lo j - rr t j) 0 ≤ α ^ t * K := by
    intro t
    induction t with
    | zero =>
      intro i j
      rw [pow_zero, one_mul]
      exact add_le_add
        (Finset.single_le_sum (f := fun i => max (rr 0 i - ss 0 - hi i) 0)
          (fun i _ => le_max_right _ _) (Finset.mem_univ i))
        (Finset.single_le_sum (f := fun j => max (ss 0 + lo j - rr 0 j) 0)
          (fun i _ => le_max_right _ _) (Finset.mem_univ j))
    | succ t ih =>
      have pair : ∀ i j, (rr (t + 1) i - ss (t + 1) - hi i) + (ss (t + 1) + lo j - rr (t + 1) j)
          ≤ α ^ (t + 1) * K := by
        intro i j
        have h1 := up1 t i
        have h2 := dn1 t j
        have h3 := ih i j
        have : α * (max (rr t i - ss t - hi i) 0 + max (ss t + lo j - rr t j) 0) ≤
            α * (α ^ t * K) := mul_le_mul_of_nonneg_left h3 hα0
        rw [pow_succ]
        nlinarith
      intro i j
      obtain ⟨i1, hi1⟩ := hA (t + 1)
      obtain ⟨j1, hj1⟩ := hB (t + 1)
      have hpow : 0 ≤ α ^ (t + 1) * K := mul_nonneg (pow_nonneg hα0 _) hK0
      rcases le_total 0 (rr (t + 1) i - ss (t + 1) - hi i) with ha | ha <;>
      rcases le_total 0 (ss (t + 1) + lo j - rr (t + 1) j) with hb' | hb'
      · rw [max_eq_left ha, max_eq_left hb']; exact pair i j
      · rw [max_eq_left ha, max_eq_right hb']; have := pair i j1; linarith
      · rw [max_eq_right ha, max_eq_left hb']; have := pair i1 j; linarith
      · rw [max_eq_right ha, max_eq_right hb']; linarith
  -- the gap between price and reference price decays geometrically
  have gap : ∀ t i, |pm (rr t) i - rr t i| ≤ α ^ t * K := by
    intro t i
    have hq := Q t i i
    have hl := hlohi i
    rw [abs_le]
    constructor
    · -- lower: r - P ≤ max (r - s - hi) 0
      have : rr t i - pm (rr t) i ≤ max (rr t i - ss t - hi i) 0 := by
        rw [hform t i]
        rcases le_or_gt (rr t i) (ss t + hi i) with h | h
        · rw [min_eq_left h]
          have := le_max_right (ss t + lo i) (rr t i)
          have := le_max_right (rr t i - ss t - hi i) 0
          linarith
        · rw [min_eq_right h.le, max_eq_right (by linarith)]
          exact le_trans (le_of_eq (by ring)) (le_max_left _ _)
      have := le_max_right (ss t + lo i - rr t i) 0
      linarith
    · have : pm (rr t) i - rr t i ≤ max (ss t + lo i - rr t i) 0 := by
        rw [hform t i]
        rcases le_or_gt (ss t + lo i) (rr t i) with h | h
        · have : max (ss t + lo i) (min (rr t i) (ss t + hi i)) ≤ rr t i :=
            max_le h (min_le_left _ _)
          have := le_max_right (ss t + lo i - rr t i) 0
          linarith
        · rw [min_eq_left (by linarith), max_eq_left h.le]
          exact le_trans (le_of_eq (by ring)) (le_max_left _ _)
      have := le_max_right (rr t i - ss t - hi i) 0
      linarith
  have hgeo : Tendsto (fun t => α ^ t * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hlt1).mul_const K
  have coord : ∀ i, ∃ R : ℝ, Tendsto (fun t => pm (rr t) i) atTop (𝓝 R) := by
    intro i
    have hcs : CauchySeq (fun t => rr t i) := by
      refine cauchySeq_of_le_geometric α K hlt1 (fun t => ?_)
      rw [Real.dist_eq, hrec, show rr t i - (α * rr t i + (1 - α) * pm (rr t) i) =
        -((1 - α) * (pm (rr t) i - rr t i)) by ring, abs_neg, abs_mul,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - α)]
      have := gap t i
      have : (1 - α) * |pm (rr t) i - rr t i| ≤ 1 * |pm (rr t) i - rr t i| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      linarith [mul_comm K (α ^ t)]
    obtain ⟨R, hR⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨R, ?_⟩
    have hd : Tendsto (fun t => pm (rr t) i - rr t i) atTop (𝓝 0) :=
      squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact gap t i) hgeo
    have := hR.add hd
    simp only [add_zero, add_sub_cancel] at this
    exact this
  choose R hR using coord
  exact ⟨R, tendsto_pi_nhds.2 hR⟩
