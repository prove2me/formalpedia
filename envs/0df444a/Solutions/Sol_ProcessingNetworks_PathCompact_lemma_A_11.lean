-- Prove2me | solution 1 for ProcessingNetworks.PathCompact.lemma_A_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:42:58.06993+00:00
-- url     : https://prove2.me/submissions/e1aa64fa-7b07-408d-a53d-0881253fdd6a

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

set_option autoImplicit false

open Filter Topology
open scoped NNReal

namespace PathCompactA11

/-- Asymptotic equicontinuity of increment-dominated monotone paths on `[0, T]`. -/
lemma asym_equi (fs gs : ℕ → ℝ≥0 → ℝ)
    (hfmono : ∀ n, Monotone (fs n))
    (hinc : ∀ n, ∀ s t : ℝ≥0, s ≤ t → fs n t - fs n s ≤ gs n t - gs n s)
    (g : ℝ≥0 → ℝ) (hgcont : Continuous g)
    (T : ℝ≥0) (hunif : TendstoUniformlyOn gs g atTop (Set.Icc 0 T))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Set.Icc (0:ℝ≥0) T, ∀ t ∈ Set.Icc (0:ℝ≥0) T,
      dist s t < δ → dist (fs n s) (fs n t) < ε := by
  have huc : UniformContinuousOn g (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hgcont.continuousOn
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 huc (ε/3) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif (ε/3) (by linarith))
  refine ⟨δ, hδ, N, fun n hn s hs t ht hst => ?_⟩
  have key : ∀ s ∈ Set.Icc (0:ℝ≥0) T, ∀ t ∈ Set.Icc (0:ℝ≥0) T, s ≤ t → dist s t < δ →
      dist (fs n s) (fs n t) < ε := by
    intro s hs t ht hle hd
    have h1 := hinc n s t hle
    have h2 := hfmono n hle
    have h3 := hδg s hs t ht hd
    have h4 := hN n hn s hs
    have h5 := hN n hn t ht
    rw [Real.dist_eq] at h3 h4 h5 ⊢
    rw [abs_lt] at h3 h4 h5 ⊢
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]
  rcases le_total s t with h | h
  · exact key s hs t ht h hst
  · rw [dist_comm] at hst ⊢; exact key t ht s hs h hst

end PathCompactA11

open Filter Topology NNReal ProcessingNetworks.PathCompact in
theorem solution (fs gs : ℕ → ℝ≥0 → ℝ)
    (hfD : ∀ n, RBMSensitivity.IsRCLL (fs n)) (hgD : ∀ n, RBMSensitivity.IsRCLL (gs n))
    (hfmono : ∀ n, Monotone (fs n)) (hgmono : ∀ n, Monotone (gs n))
    (hf0 : ∀ n, fs n 0 = 0) (hg0 : ∀ n, gs n 0 = 0)
    (hinc : ∀ n, ∀ s t : ℝ≥0, s ≤ t → fs n t - fs n s ≤ gs n t - gs n s)
    (g : ℝ≥0 → ℝ) (hgcont : Continuous g) (hconv : ConvergesUOC gs g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ≥0 → ℝ, Continuous f ∧
      ConvergesUOC (fun k => fs (φ k)) f := by
  have hc := hconv
  unfold ConvergesUOC at hc
  obtain ⟨_, _, hgU⟩ := hc
  have hz : ∀ x : ℝ≥0, 0 ≤ x := fun x => by positivity
  have hpt : ∀ x : ℝ≥0, Tendsto (fun n => gs n x) atTop (𝓝 (g x)) := by
    intro x
    exact (hgU (x+1) (by positivity)).tendsto_at ⟨hz x, le_self_add⟩
  have hnn : ∀ n x, 0 ≤ fs n x := fun n x => by
    simpa [hf0 n] using hfmono n (hz x)
  have hle : ∀ n x, fs n x ≤ gs n x := fun n x => by
    simpa [hf0 n, hg0 n] using hinc n 0 x (hz x)
  have hB : ∀ x : ℝ≥0, ∃ B, ∀ n, fs n x ≤ B := by
    intro x
    obtain ⟨B, hB⟩ := (hpt x).bddAbove_range
    exact ⟨B, fun n => (hle n x).trans (hB ⟨n, rfl⟩)⟩
  choose B hBB using hB
  let r : ℚ → ℝ≥0 := fun q => Real.toNNReal q
  let X : ℕ → (∀ q : ℚ, Set.Icc (0:ℝ) (B (r q))) := fun n q => ⟨fs n (r q), hnn n _, hBB _ n⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq X
  have hcq : ∀ q : ℚ, CauchySeq (fun k => fs (φ k) (r q)) := by
    intro q
    have h1 := (continuous_subtype_val.tendsto _).comp (((continuous_apply q).tendsto a).comp hlim)
    exact h1.cauchySeq
  have hUC : ∀ T : ℝ≥0, 0 < T → UniformCauchySeqOn (fun k => fs (φ k)) atTop (Set.Icc 0 T) := by
    intro T hT
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, N1, hN1⟩ :=
      PathCompactA11.asym_equi fs gs hfmono hinc g hgcont T (hgU T hT) (ε/3) (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    have hM : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hev : ∀ᶠ p : ℕ × ℕ in atTop, ∀ j ∈ Finset.range (⌊(T:ℝ) * ((m:ℝ) + 1)⌋₊ + 1),
        dist (fs (φ p.1) (r ((j:ℚ) / ((m:ℚ) + 1)))) (fs (φ p.2) (r ((j:ℚ) / ((m:ℚ) + 1)))) < ε/3 := by
      rw [Filter.eventually_all_finset]
      intro j _
      have h1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (hcq ((j:ℚ) / ((m:ℚ) + 1)))
      exact (tendsto_order.1 h1).2 _ (by linarith)
    obtain ⟨⟨a1, a2⟩, ha⟩ := eventually_atTop.1 hev
    refine ⟨max N1 (max a1 a2), fun k hk l hl t ht => ?_⟩
    have ht0 : (0:ℝ) ≤ (t:ℝ) * ((m:ℝ) + 1) := by positivity
    set j := ⌊(t:ℝ) * ((m:ℝ) + 1)⌋₊ with hjdef
    have hj1 : (j:ℝ) ≤ (t:ℝ) * ((m:ℝ) + 1) := Nat.floor_le ht0
    have hj2 : (t:ℝ) * ((m:ℝ) + 1) < (j:ℝ) + 1 := Nat.lt_floor_add_one _
    have htT : (t:ℝ) ≤ (T:ℝ) := by exact_mod_cast ht.2
    have hj : j ∈ Finset.range (⌊(T:ℝ) * ((m:ℝ) + 1)⌋₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right htT hM.le)
    set q : ℝ≥0 := r ((j:ℚ) / ((m:ℚ) + 1)) with hqdef
    have hq : (q:ℝ) = (j:ℝ) / ((m:ℝ) + 1) := by
      rw [hqdef]
      simp only [r]
      rw [Real.coe_toNNReal _ (by positivity)]
      push_cast
      ring
    have hqt : (q:ℝ) ≤ t := by
      rw [hq, div_le_iff₀ hM]; exact hj1
    have hqI : q ∈ Set.Icc (0:ℝ≥0) T := ⟨hz _, by
      have : (q:ℝ) ≤ T := hqt.trans htT
      exact_mod_cast this⟩
    have hdist : dist q t < δ := by
      rw [NNReal.dist_eq, abs_lt]
      have h1 : (t:ℝ) - (q:ℝ) < 1 / ((m:ℝ) + 1) := by
        rw [hq, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hM]
        linarith
      constructor <;> linarith
    have hk1 : N1 ≤ φ k := (le_trans (le_max_left _ _) hk).trans (hφ.id_le k)
    have hl1 : N1 ≤ φ l := (le_trans (le_max_left _ _) hl).trans (hφ.id_le l)
    have e1 := hN1 (φ k) hk1 q hqI t ht hdist
    have e2 := hN1 (φ l) hl1 q hqI t ht hdist
    have e3 := ha (k, l) (Prod.mk_le_mk.2
      ⟨(le_max_left _ _).trans ((le_max_right _ _).trans hk),
       (le_max_right _ _).trans ((le_max_right _ _).trans hl)⟩) j hj
    have e3' : dist (fs (φ k) q) (fs (φ l) q) < ε/3 := e3
    rw [dist_comm] at e1
    calc dist (fs (φ k) t) (fs (φ l) t)
        ≤ dist (fs (φ k) t) (fs (φ k) q) + dist (fs (φ k) q) (fs (φ l) q)
          + dist (fs (φ l) q) (fs (φ l) t) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  have hcs : ∀ t : ℝ≥0, CauchySeq (fun k => fs (φ k) t) := by
    intro t
    exact (hUC (t+1) (by positivity)).cauchySeq ⟨hz _, le_self_add⟩
  choose f hf using fun t => cauchySeq_tendsto_of_complete (hcs t)
  have hfc : Continuous f := by
    rw [Metric.continuous_iff]
    intro t ε hε
    obtain ⟨δ, hδ, N1, hN1⟩ := PathCompactA11.asym_equi fs gs hfmono hinc g hgcont (t+1)
      (hgU _ (by positivity)) (ε/2) (by linarith)
    refine ⟨min δ 1, by positivity, fun s hs => ?_⟩
    have hs1 : (s:ℝ) ≤ (t:ℝ) + 1 := by
      have h1 := lt_of_lt_of_le hs (min_le_right _ _)
      rw [NNReal.dist_eq, abs_lt] at h1
      linarith
    have hsI : s ∈ Set.Icc 0 (t+1) := ⟨hz _, by exact_mod_cast hs1⟩
    have htI : t ∈ Set.Icc 0 (t+1) := ⟨hz _, le_self_add⟩
    have hlim2 : Tendsto (fun k => dist (fs (φ k) s) (fs (φ k) t)) atTop
        (𝓝 (dist (f s) (f t))) := (hf s).dist (hf t)
    have h2 : dist (f s) (f t) ≤ ε/2 := le_of_tendsto hlim2
      (eventually_atTop.2 ⟨N1, fun k hk => (hN1 (φ k) (hk.trans (hφ.id_le k)) s hsI t htI
        (lt_of_lt_of_le hs (min_le_left _ _))).le⟩)
    linarith
  refine ⟨φ, hφ, f, hfc, ?_⟩
  unfold ConvergesUOC
  refine ⟨fun k => hfD (φ k), ?_, fun T hT => ?_⟩
  · intro t
    exact ⟨hfc.continuousAt.continuousWithinAt, f t,
      hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  · exact (hUC T hT).tendstoUniformlyOn_of_tendsto (fun t _ => hf t)
