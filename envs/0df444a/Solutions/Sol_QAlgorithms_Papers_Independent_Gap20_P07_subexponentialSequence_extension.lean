-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P07.subexponentialSequence_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:02:30.829021+00:00
-- url     : https://prove2.me/submissions/f45748e8-d85d-441e-90f9-9c359cb3dba0

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap20.P07
open QAlgorithms
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)
open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsDensity)


theorem g79e_anti_n (f : ℕ+ → ℕ+ → ℝ≥0∞) (h : ∀ n m, f (n + 1) m ≤ f n m) (m : ℕ+) :
    ∀ n n' : ℕ+, n ≤ n' → f n' m ≤ f n m := by
  have hF : Antitone (fun k : ℕ => f (Nat.toPNat' k) m) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_of_eq rfl
    · have : Nat.toPNat' (k + 1) = Nat.toPNat' k + 1 := by
        apply PNat.eq
        rw [PNat.add_coe, Nat.toPNat'_coe, Nat.toPNat'_coe, if_pos (by omega), if_pos hk]
        rfl
      rw [this]; exact h _ _
  intro n n' hnn
  have := hF (show (n : ℕ) ≤ (n' : ℕ) from hnn)
  simpa using this

theorem g79e_mono_m (f : ℕ+ → ℕ+ → ℝ≥0∞) (h : ∀ n m, f n m ≤ f n (m + 1)) (n : ℕ+) :
    ∀ m m' : ℕ+, m ≤ m' → f n m ≤ f n m' := by
  have hF : Monotone (fun k : ℕ => f n (Nat.toPNat' k)) := by
    refine monotone_nat_of_le_succ (fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_of_eq rfl
    · have : Nat.toPNat' (k + 1) = Nat.toPNat' k + 1 := by
        apply PNat.eq
        rw [PNat.add_coe, Nat.toPNat'_coe, Nat.toPNat'_coe, if_pos (by omega), if_pos hk]
        rfl
      rw [this]; exact h _ _
  intro m m' hmm
  have := hF (show (m : ℕ) ≤ (m' : ℕ) from hmm)
  simpa using this

theorem g79e_ratio' (M N : ℕ+) : ((M : ℝ≥0∞) / (N : ℝ≥0∞)) = ENNReal.ofReal ((M : ℝ) / (N : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp

theorem solution (delta : ℕ+ → ℕ+ → ℝ≥0)
    (hmono : ErrorMonotone (fun n m => (delta n m : ℝ≥0∞)))
    (N M : ℕ → ℕ+)
    (hN : Tendsto (fun a => (N a : ℕ)) atTop atTop)
    (hratio : Tendsto (fun a => (N (a + 1) : ℝ) / (N a : ℝ)) atTop (𝓝 1))
    (herror : Tendsto (fun a => delta (N a) (M a)) atTop (𝓝 0))
    (n m : ℕ → ℕ+) (hn : Tendsto (fun a => (n a : ℕ)) atTop atTop)
    (hrate : Filter.limsup (rateRatio n m) atTop < Filter.liminf (rateRatio N M) atTop) :
    Tendsto (fun a => delta (n a) (m a)) atTop (𝓝 0) := by
  obtain ⟨r1, hL1, h12⟩ := exists_between hrate
  obtain ⟨r2, h12', h2L⟩ := exists_between h12
  have hr1top : r1 ≠ ⊤ := ne_top_of_lt h12'
  have hr2top : r2 ≠ ⊤ := ne_top_of_lt h2L
  have hr1pos : 0 < r1 := lt_of_le_of_lt bot_le hL1
  set s1 := r1.toReal
  set s2 := r2.toReal
  have hs1 : 0 < s1 := ENNReal.toReal_pos hr1pos.ne' hr1top
  have hs12 : s1 < s2 := (ENNReal.toReal_lt_toReal hr1top hr2top).mpr h12'
  have hs2 : 0 < s2 := hs1.trans hs12
  -- small sequence rate
  have hA : ∀ᶠ a in atTop, ((m a : ℕ) : ℝ) < s1 * (n a : ℕ) := by
    filter_upwards [Filter.eventually_lt_of_limsup_lt hL1] with a ha
    simp only [rateRatio] at ha
    rw [g79e_ratio', ← ENNReal.ofReal_toReal hr1top,
      ENNReal.ofReal_lt_ofReal_iff hs1] at ha
    have hn0 : (0 : ℝ) < (n a : ℕ) := by exact_mod_cast (n a).pos
    have := (div_lt_iff₀ hn0).mp ha
    simpa [mul_comm] using this
  have hB1 : ∀ᶠ b in atTop, s2 * (N b : ℕ) < ((M b : ℕ) : ℝ) := by
    filter_upwards [Filter.eventually_lt_of_lt_liminf h2L] with b hb
    simp only [rateRatio] at hb
    rw [g79e_ratio', ← ENNReal.ofReal_toReal hr2top,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg] at hb
    have hN0 : (0 : ℝ) < (N b : ℕ) := by exact_mod_cast (N b).pos
    have := (lt_div_iff₀ hN0).mp hb
    simpa using this
  have hB2 : ∀ᶠ b in atTop, ((N (b + 1) : ℕ) : ℝ) / (N b : ℕ) < s2 / s1 :=
    hratio.eventually (gt_mem_nhds ((one_lt_div hs1).mpr hs12))
  obtain ⟨B0, hB0⟩ := Filter.eventually_atTop.mp (hB1.and hB2)
  -- the index map
  have hK : ∀ a, ∃ K, ∀ b ≥ K, (n a : ℕ) < (N b : ℕ) := fun a =>
    Filter.eventually_atTop.mp (hN.eventually (Filter.eventually_gt_atTop (n a : ℕ)))
  choose K hKspec using hK
  let β : ℕ → ℕ := fun a => Nat.findGreatest (fun b => (N b : ℕ) ≤ (n a : ℕ)) (K a)
  have hge : ∀ B, ∀ᶠ a in atTop, B ≤ β a ∧ (N (β a) : ℕ) ≤ (n a : ℕ) ∧ (n a : ℕ) < (N (β a + 1) : ℕ) := by
    intro B
    have hev : ∀ᶠ a in atTop, ∀ b ≤ B, (N b : ℕ) ≤ (n a : ℕ) := by
      filter_upwards [hn.eventually (Filter.eventually_ge_atTop
        ((Finset.range (B + 1)).sup (fun b => (N b : ℕ))))] with a ha b hb
      exact le_trans (Finset.le_sup (f := fun b => (N b : ℕ))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))) ha
    filter_upwards [hev] with a ha
    have hPB : (N B : ℕ) ≤ (n a : ℕ) := ha B le_rfl
    have hBK : B ≤ K a := by
      by_contra hc; push_neg at hc
      exact absurd hPB (not_le.mpr (hKspec a B hc.le))
    have h1 : B ≤ β a := Nat.le_findGreatest hBK hPB
    refine ⟨h1, Nat.findGreatest_spec (P := fun b => (N b : ℕ) ≤ (n a : ℕ)) hBK hPB, ?_⟩
    by_contra hc; push_neg at hc
    by_cases hk : β a + 1 ≤ K a
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hk hc
    · push_neg at hk
      exact absurd hc (not_le.mpr (hKspec a _ (by omega)))
  have hβ : Tendsto β atTop atTop := by
    refine Filter.tendsto_atTop.mpr (fun B => ?_)
    filter_upwards [hge B] with a ha using ha.1
  have hbound : ∀ᶠ a in atTop, delta (n a) (m a) ≤ delta (N (β a)) (M (β a)) := by
    filter_upwards [hge B0, hA] with a ha hma
    obtain ⟨hb, hNn, hnN⟩ := ha
    obtain ⟨h1, h2⟩ := hB0 (β a) hb
    have hN0 : (0 : ℝ) < (N (β a) : ℕ) := by exact_mod_cast (N (β a)).pos
    have h2' : ((N (β a + 1) : ℕ) : ℝ) < s2 / s1 * (N (β a) : ℕ) := (div_lt_iff₀ hN0).mp h2
    have hnN' : ((n a : ℕ) : ℝ) < (N (β a + 1) : ℕ) := by exact_mod_cast hnN
    have hmM : ((m a : ℕ) : ℝ) < (M (β a) : ℕ) := by
      have e : s1 * (s2 / s1 * (N (β a) : ℕ)) = s2 * (N (β a) : ℕ) := by field_simp
      nlinarith
    have hmM' : m a ≤ M (β a) := by
      have : (m a : ℕ) < (M (β a) : ℕ) := by exact_mod_cast hmM
      exact_mod_cast this.le
    have hx := g79e_anti_n (fun n m => (delta n m : ℝ≥0∞)) (fun n m => (hmono n m).1) (m a)
      (N (β a)) (n a) (by exact_mod_cast hNn)
    have hy := g79e_mono_m (fun n m => (delta n m : ℝ≥0∞)) (fun n m => (hmono n m).2) (N (β a))
      (m a) (M (β a)) hmM'
    exact_mod_cast hx.trans hy
  rw [← NNReal.tendsto_coe]
  have hlim : Tendsto (fun a => ((delta (N (β a)) (M (β a)) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    exact (NNReal.tendsto_coe.mpr herror).comp hβ
  refine squeeze_zero' (Filter.Eventually.of_forall fun a => NNReal.coe_nonneg _) ?_ hlim
  filter_upwards [hbound] with a ha
  exact_mod_cast ha
