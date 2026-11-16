-- Prove2me | solution 1 for RGMISFast.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T22:18:36.425525+00:00
-- url     : https://prove2.me/submissions/2696cb5e-909d-4326-85b9-3fff8c45ed10

import Theorems.Thm_RGMISFast_low_rank_fixed_size_tail
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma low_rank_exp_sum (L : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, Real.exp (-(j:ℝ)-L-2)) ≤ Real.exp (-L)/4 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hq : Real.exp (-1) ≤ (2/5:ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr
    norm_num
    linarith
  have hsum : ∀ n, (∑j∈Finset.range n,Real.exp (-(j:ℝ))) ≤ (5/3:ℝ) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have hid : ∀j:ℕ,Real.exp (-((j+1:ℕ):ℝ)) = Real.exp (-1)*Real.exp (-(j:ℝ)) := by
        intro j; rw [← Real.exp_add]; congr 1; push_cast; ring
      simp_rw [hid]
      rw [← Finset.mul_sum]
      have hm := mul_le_mul_of_nonneg_left ih (Real.exp_pos (-1)).le
      norm_num
      nlinarith
  have hfactor : (∑j∈Finset.range n,Real.exp (-(j:ℝ)-L-2)) =
      Real.exp (-L-2)*(∑j∈Finset.range n,Real.exp (-(j:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Real.exp_add]
    congr 1; ring
  rw [hfactor]
  have hs := mul_le_mul_of_nonneg_left (hsum n) (Real.exp_pos (-L-2)).le
  have hexp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he2 : (20/3:ℝ) ≤ Real.exp 2 := by rw [hexp]; nlinarith
  have hratio : Real.exp (-2)*(5/3:ℝ) ≤ 1/4 := by
    rw [Real.exp_neg]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (Real.exp_pos 2)).mpr
    linarith
  have hid : Real.exp (-L-2) = Real.exp (-L)*Real.exp (-2) := by
    rw [← Real.exp_add]; congr 1
  rw [hid] at hs ⊢
  have hm := mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-L)).le
  nlinarith

lemma low_rank_threshold_bound (Δ j : ℕ) (hΔ : 2 ≤ Δ) (L : ℝ) :
    (8*(Δ:ℝ))^j*(1/2:ℝ)^⌈((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2⌉₊ ≤
      Real.exp (-(j:ℝ)-L-2) := by
  have hd : 0 < (Δ:ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < 8*(Δ:ℝ) := by positivity
  have hbudget := (div_le_iff₀ hlog).mp (Nat.le_ceil
    (((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2))
  have hlogs : Real.log (8*Real.exp 1*Δ) = Real.log (8*(Δ:ℝ))+1 := by
    rw [show 8*Real.exp 1*(Δ:ℝ) = (8*(Δ:ℝ))*Real.exp 1 by ring,
      Real.log_mul (ne_of_gt hb) (Real.exp_ne_zero 1), Real.log_exp]
  have hid (k : ℕ) : (8*(Δ:ℝ))^j*(1/2:ℝ)^k =
      Real.exp ((j:ℝ)*Real.log (8*(Δ:ℝ))-(k:ℝ)*Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hb, Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp [div_eq_mul_inv]
  rw [hid]
  apply Real.exp_le_exp.mpr
  rw [hlogs] at hbudget ⊢
  nlinarith

/-- The all-sizes argument, with the fixed-size probability estimate explicit. -/
theorem low_rank_all_sizes {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (u : V) (L : ℝ) (hL : 8 ≤ L)
    (hfixed : ∀j k:ℕ,1 ≤ k →
      rankLaw V {r | ∃A:Finset V, IsRootConnected G u A ∧ A.card=j+1 ∧
        k ≤ (GammaLow G r Δ A).card} ≤ ENNReal.ofReal ((8*(Δ:ℝ))^j*(1/2:ℝ)^k)) :
    rankLaw V {r | ¬ LowRankEvent G Δ u L r} ≤ ENNReal.ofReal (Real.exp (-L)/4) := by
  classical
  let k := fun j:ℕ => ⌈((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2⌉₊
  let E := fun j:ℕ => {r : V → ℝ | ∃A:Finset V, IsRootConnected G u A ∧ A.card=j+1 ∧
    k j ≤ (GammaLow G r Δ A).card}
  have hd : 2 ≤ (Δ:ℝ) := by exact_mod_cast hΔ
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hB : 1 ≤ 8*Real.exp 1*(Δ:ℝ) := by nlinarith
  have hlogB : 0 ≤ Real.log (8*Real.exp 1*Δ) := Real.log_nonneg hB
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hk : ∀j,1 ≤ k j := by
    intro j
    have hnum : 0 < (j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2 := by positivity
    have hp : 0 < ((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2 := div_pos hnum hlog2pos
    have hh := Nat.le_ceil (((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2)
    have hn : 0 < (k j:ℝ) := lt_of_lt_of_le hp hh
    exact_mod_cast (show (1:ℕ) ≤ k j by exact Nat.succ_le_of_lt (by exact_mod_cast hn))
  have hsub : {r | ¬ LowRankEvent G Δ u L r} ⊆ ⋃j∈Finset.range (Fintype.card V),E j := by
    intro r hr
    change ¬ (∀A,IsRootConnected G u A → _) at hr
    push_neg at hr
    obtain ⟨A,hA,hbad⟩ := hr
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨u,hA.1⟩
    let j := A.card-1
    have hj : A.card = j+1 := by dsimp [j]; omega
    have hjbound : j < Fintype.card V := by have hh := Finset.card_le_univ A; omega
    refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjbound,A,hA,hj,?_⟩⟩
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hlog2pos).mpr
    have hnum : 0 ≤ (j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2 := by positivity
    have hcard : 0 ≤ ((GammaLow G r Δ A).card:ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hlog2 hcard
    have hjreal : (A.card:ℝ) = (j:ℝ)+1 := by exact_mod_cast hj
    rw [hjreal] at hbad
    nlinarith
  have hE : ∀j,rankLaw V (E j) ≤ ENNReal.ofReal (Real.exp (-(j:ℝ)-L-2)) := by
    intro j
    exact (hfixed j (k j) (hk j)).trans (ENNReal.ofReal_le_ofReal (low_rank_threshold_bound Δ j hΔ L))
  calc
    _ ≤ rankLaw V (⋃j∈Finset.range (Fintype.card V),E j) := measure_mono hsub
    _ ≤ ∑j∈Finset.range (Fintype.card V),rankLaw V (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑j∈Finset.range (Fintype.card V),ENNReal.ofReal (Real.exp (-(j:ℝ)-L-2)) :=
      Finset.sum_le_sum (fun j _ => hE j)
    _ = ENNReal.ofReal (∑j∈Finset.range (Fintype.card V),Real.exp (-(j:ℝ)-L-2)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (low_rank_exp_sum L (Fintype.card V))

open RGMISFast

/-- Lemma A.1 (Low Ranks; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.29): with probability at least `1 − e^{−L}/4`, every
root-connected set `A` satisfies `|Γ_{<a_M}(A)| ≤ 2(|A| log(8e∆) + L + 2)` (32).

**Formalization Note** `L = h + 8` with `h ≥ 0` ("Fix L = h + 8 as in Section 3", p.29), stated
for every real `L ≥ 8`. The bad event `¬ LowRankEvent` has (outer) measure at most `e^{−L}/4`
under the i.i.d. Exp(1) rank law. `log` is the natural logarithm; `M = Mof Δ`; all degrees are at
most `∆`, `∆ ≥ 2`. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (L : ℝ)
    (hL : 8 ≤ L) :
    rankLaw V {r | ¬ LowRankEvent G Δ u L r} ≤ ENNReal.ofReal (Real.exp (-L) / 4) := by
  exact low_rank_all_sizes G Δ hΔ u L hL (fun j k hk =>
    low_rank_fixed_size_tail G Δ hΔ hdeg u j k hk)


