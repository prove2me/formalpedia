-- Prove2me | solution 1 for RGMISFast.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T22:46:21.524758+00:00
-- url     : https://prove2.me/submissions/d686ceb7-4054-482e-884c-4471d483aa4e

import Theorems.Thm_RGMISFast_entries_growth_level_tail
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw

open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma entries_band_factor_gt_one : 1 < c := by
  unfold c
  have h : 0 < 1/(2*Real.exp 2) := by positivity
  linarith

lemma entries_am_pos (n : ℕ) : 0 < am n := by
  have hc : 0 < c := lt_trans (by norm_num) entries_band_factor_gt_one
  unfold am a0
  positivity

lemma entries_am_step (n : ℕ) : am n = c*am (n+1) := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) entries_band_factor_gt_one).ne'
  unfold am
  rw [pow_succ]
  field_simp

lemma entries_weighted_band_sum (N : ℕ) :
    (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) ≤ 4*(Real.exp 2)^3+4*(Real.exp 2)^2 := by
  have hc := entries_band_factor_gt_one
  have hden : 0 < (c-1)^2 := sq_pos_of_pos (by linarith)
  have hid : ∀N:ℕ, (c-1)^2*(∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1))+
      am N*(((N:ℝ)+2)*c-((N:ℝ)+1)) = a0*(2*c-1) := by
    intro N
    induction N with
    | zero => simp [am]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [entries_am_step N] at ih
      nlinarith only [ih]
  have htail : 0 ≤ am N*(((N:ℝ)+2)*c-((N:ℝ)+1)) := by
    apply mul_nonneg (entries_am_pos N).le
    have hm := mul_le_mul_of_nonneg_left hc.le (show 0 ≤ (N:ℝ)+2 by positivity)
    linarith
  have hsum : (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) ≤ a0*(2*c-1)/(c-1)^2 := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hid N,htail]
  have he : a0*(2*c-1)/(c-1)^2 = 4*(Real.exp 2)^3+4*(Real.exp 2)^2 := by
    unfold a0 c
    have hp : Real.exp 2 ≠ 0 := Real.exp_ne_zero 2
    field_simp
    ring
  exact hsum.trans_eq he

lemma entries_total_budget (N : ℕ) (L : ℝ) :
    (∑n∈Finset.range N, ((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) ≤
      320*Real.exp (-L) := by
  have hcoef : 0 ≤ Real.exp (-2)+2*Real.exp (-4) := by positivity
  have hs := mul_le_mul_of_nonneg_left (entries_weighted_band_sum N)
    (mul_nonneg hcoef (Real.exp_pos (-L)).le)
  have hsum : (∑n∈Finset.range N, ((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) =
      ((Real.exp (-2)+2*Real.exp (-4))*Real.exp (-L)) *
        (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn; ring
  rw [hsum]
  have hfour : Real.exp (-4) = ((Real.exp 2)^2)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]
    norm_num
  have heq : (Real.exp (-2)+2*Real.exp (-4))*(4*(Real.exp 2)^3+4*(Real.exp 2)^2) =
      4*(Real.exp 2+1)*(Real.exp 2+2) := by
    rw [hfour,Real.exp_neg]
    have hp : Real.exp 2 ≠ 0 := Real.exp_ne_zero 2
    field_simp
  have he2 : Real.exp 2 ≤ (37/5:ℝ) := by
    have he1 := Real.exp_one_lt_d9
    have hepos := Real.exp_pos 1
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [←Real.exp_add]; norm_num
    rw [he]; nlinarith
  have hnum : 4*(Real.exp 2+1)*(Real.exp 2+2) ≤ 320 := by
    have hm := mul_le_mul (show Real.exp 2+1 ≤ (42/5:ℝ) by linarith)
      (show Real.exp 2+2 ≤ (47/5:ℝ) by linarith)
      (by positivity : 0 ≤ Real.exp 2+2) (by norm_num : (0:ℝ) ≤ 42/5)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hnum (Real.exp_pos (-L)).le
  have heq' := congrArg (fun x:ℝ => x*Real.exp (-L)) heq
  nlinarith only [hs,hm,heq']
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

/-- The finite union over levels, with the per-level probability bound explicit. -/
theorem entries_growth_from_levels {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (u : V) (L : ℝ)
    (hlevel : ∀m:ℕ,1 ≤ m → m ≤ Mof Δ →
      rankLaw V {r | (∃A:Finset V, IsRootConnected G u A ∧ ActiveAt G r (am m) A ∧
          2*Sm r A m+L < ((Gammam G r m A).card:ℝ)) ∨
        (∃i:ℕ,i < m ∧ ∃B:Finset V, IsRootConnected G u B ∧ ActiveAt G r (am m) B ∧
          32*c^(1+m-i)*(2*Sm r B m+L) < (Kmi G r m i B:ℝ))} ≤
      ENNReal.ofReal (((m:ℝ)+1)*(Real.exp (-2)+2*Real.exp (-4))*am m*Real.exp (-L))) :
    rankLaw V {r | ¬ (EntryEvent G Δ u L r ∧ GrowthEvent G Δ u L r)} ≤
      ENNReal.ofReal (320*Real.exp (-L)) := by
  classical
  let E := fun m:ℕ => {r : V → ℝ | (∃A:Finset V, IsRootConnected G u A ∧ ActiveAt G r (am m) A ∧
          2*Sm r A m+L < ((Gammam G r m A).card:ℝ)) ∨
        (∃i:ℕ,i < m ∧ ∃B:Finset V, IsRootConnected G u B ∧ ActiveAt G r (am m) B ∧
          32*c^(1+m-i)*(2*Sm r B m+L) < (Kmi G r m i B:ℝ))}
  have hsub : {r | ¬ (EntryEvent G Δ u L r ∧ GrowthEvent G Δ u L r)} ⊆
      ⋃n∈Finset.range (Mof Δ),E (n+1) := by
    intro r hr
    rcases not_and_or.mp hr with he | hg
    · unfold EntryEvent at he
      push_neg at he
      obtain ⟨m,i,him,hm,B,hB,hact,hbad⟩ := he
      have hmpos : 1 ≤ m := by omega
      refine Set.mem_iUnion.mpr ⟨m-1,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
      rw [Nat.sub_add_cancel hmpos]
      exact Or.inr ⟨i,him,B,hB,hact,hbad⟩
    · unfold GrowthEvent at hg
      push_neg at hg
      obtain ⟨m,hmpos,hm,A,hA,hact,hbad⟩ := hg
      refine Set.mem_iUnion.mpr ⟨m-1,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
      rw [Nat.sub_add_cancel hmpos]
      exact Or.inl ⟨A,hA,hact,hbad⟩
  have heach : ∀n∈Finset.range (Mof Δ),rankLaw V (E (n+1)) ≤
      ENNReal.ofReal (((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) := by
    intro n hn
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      hlevel (n+1) (by omega) (by have hh := Finset.mem_range.mp hn; omega)
  calc
    _ ≤ rankLaw V (⋃n∈Finset.range (Mof Δ),E (n+1)) := measure_mono hsub
    _ ≤ ∑n∈Finset.range (Mof Δ),rankLaw V (E (n+1)) := measure_biUnion_finset_le _ _
    _ ≤ ∑n∈Finset.range (Mof Δ),
        ENNReal.ofReal (((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) :=
      Finset.sum_le_sum heach
    _ = ENNReal.ofReal (∑n∈Finset.range (Mof Δ),
        ((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro n hn
      have hp := entries_am_pos (n+1)
      positivity
    _ ≤ _ := ENNReal.ofReal_le_ofReal (entries_total_budget (Mof Δ) L)
open RGMISFast

/-- Lemma 3.1 (Entries and Growth; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.14, proof in §6.2): fix a deviation parameter
`L ≥ 8`; with probability at least `1 − 320e^{−L}`, both (a) for every `0 ≤ i < m ≤ M` and every
root-connected `B` active at `a_m`, `K_{m,i}(B) ≤ 32c^{1+m−i}(2S_m(B) + L)` (9), and (b) for every
`1 ≤ m ≤ M` and every root-connected `A` active at `a_m`, `|Γ_m(A)| ≤ 2S_m(A) + L` (10), hold.

**Formalization Note** One bad event for (a) and (b) jointly, of (outer) measure at most
`320e^{−L}` under the i.i.d. Exp(1) rank law. `M = Mof Δ`; all degrees at most `∆`, `∆ ≥ 2`
(the setting of Theorem 1.1, which fixes `M`). -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (L : ℝ)
    (hL : 8 ≤ L) :
    rankLaw V {r | ¬ (EntryEvent G Δ u L r ∧ GrowthEvent G Δ u L r)} ≤
      ENNReal.ofReal (320 * Real.exp (-L)) := by
  exact entries_growth_from_levels G Δ u L
    (entries_growth_level_tail G Δ hΔ hdeg u L hL)


