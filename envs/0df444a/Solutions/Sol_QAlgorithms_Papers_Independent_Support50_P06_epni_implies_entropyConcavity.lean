-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P06.epni_implies_entropyConcavity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:01:10.499689+00:00
-- url     : https://prove2.me/submissions/0e5496a7-521a-4551-a299-507aa50b9fa9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

namespace X7L3EC

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

lemma X7_g_zero : g 0 = 0 := by simp [g]

lemma X7_g_cont : ContinuousOn g (Set.Ici 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
    apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
  exact h1.sub Real.continuous_mul_log.continuousOn

lemma X7_g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

lemma X7_g_strictMono : StrictMonoOn g (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) X7_g_cont
  intro x hx
  rw [interior_Ici] at hx
  rw [(X7_g_hasDeriv hx).deriv]
  have := Real.log_lt_log hx (by linarith : x < x + 1)
  linarith

lemma X7_g_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

lemma X7_g_concave : ConcaveOn ℝ (Set.Ici 0) g := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) X7_g_cont
  · rw [interior_Ici]; intro x hx
    exact (X7_g_hasDeriv hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    rw [(X7_g_hasDeriv ha').deriv, (X7_g_hasDeriv hb').deriv]
    rw [← Real.log_div (by linarith) ha'.ne', ← Real.log_div (by linarith) hb'.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hb' ha']
    nlinarith

lemma X7_spec {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ thermalEntropyInverse s ∧ g (thermalEntropyInverse s) = s := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0; simp [thermalEntropyInverse, X7_g_zero]
  have he : 0 ≤ Real.exp s := (Real.exp_pos s).le
  have hmem : s ∈ Set.Icc (g 0) (g (Real.exp s)) := by
    refine ⟨by rw [X7_g_zero]; exact hs, ?_⟩
    have h1 := X7_g_ge_log he
    have h2 : s ≤ Real.log (Real.exp s + 1) := by
      rw [← Real.log_exp s]
      exact Real.log_le_log (Real.exp_pos _) (by rw [Real.log_exp]; linarith)
    linarith
  obtain ⟨N, ⟨hN0, -⟩, hgN⟩ :=
    intermediate_value_Icc he (X7_g_cont.mono Set.Icc_subset_Ici_self) hmem
  have hinv : thermalEntropyInverse s = N := by
    unfold thermalEntropyInverse
    rw [if_neg (not_le.2 hpos)]
    apply IsLeast.csInf_eq
    refine ⟨⟨hN0, ?_⟩, ?_⟩
    · show s ≤ g N; rw [hgN]
    · rintro M ⟨hM0, hM⟩
      have hM' : s ≤ g M := hM
      exact (X7_g_strictMono.le_iff_le hN0 hM0).1 (hgN ▸ hM')
  rw [hinv]; exact ⟨hN0, hgN⟩

end X7L3EC

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P06 X7L3EC in
theorem solution (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (rhoA rhoB : State (NumberString n))
    (hA : spectralEntropyNats rhoA.coefficients ≠ ⊤)
    (hB : spectralEntropyNats rhoB.coefficients ≠ ⊤)
    (hepni : EpniAt eta rhoA.coefficients rhoB.coefficients) :
    ENNReal.ofReal eta * spectralEntropyNats rhoA.coefficients +
        ENNReal.ofReal (1 - eta) * spectralEntropyNats rhoB.coefficients ≤
      spectralEntropyNats (mixedOutput n eta rhoA.coefficients rhoB.coefficients) := by
  set SA := spectralEntropyNats rhoA.coefficients with hSA
  set SB := spectralEntropyNats rhoB.coefficients with hSB
  set SC := spectralEntropyNats (mixedOutput n eta rhoA.coefficients rhoB.coefficients) with hSC
  by_cases hC : SC = ⊤
  · rw [hC]; exact le_top
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  unfold EpniAt entropyPhotonNumber entropyParameter at hepni
  rw [← hSA, ← hSB, ← hSC, if_neg hA, if_neg hB, if_neg hC] at hepni
  obtain ⟨hNA0, hgA⟩ := X7_spec (s := SA.toReal / n) (by positivity)
  obtain ⟨hNB0, hgB⟩ := X7_spec (s := SB.toReal / n) (by positivity)
  obtain ⟨hNC0, hgC⟩ := X7_spec (s := SC.toReal / n) (by positivity)
  set NA := thermalEntropyInverse (SA.toReal / n)
  set NB := thermalEntropyInverse (SB.toReal / n)
  set NC := thermalEntropyInverse (SC.toReal / n)
  have h1e : 0 ≤ 1 - eta := by linarith
  rw [← ENNReal.ofReal_mul heta, ← ENNReal.ofReal_mul h1e,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff hNC0] at hepni
  have hmix : 0 ≤ eta * NA + (1 - eta) * NB := by positivity
  have hmono : g (eta * NA + (1 - eta) * NB) ≤ g NC :=
    X7_g_strictMono.monotoneOn hmix hNC0 hepni
  have hconc := X7_g_concave.2 (x := NA) (y := NB) hNA0 hNB0 heta h1e (by ring)
  simp only [smul_eq_mul] at hconc
  rw [hgA, hgB] at hconc
  rw [hgC] at hmono
  have hreal : eta * SA.toReal + (1 - eta) * SB.toReal ≤ SC.toReal := by
    have := le_trans hconc hmono
    have h2 : eta * (SA.toReal / n) + (1 - eta) * (SB.toReal / n) =
        (eta * SA.toReal + (1 - eta) * SB.toReal) / n := by ring
    rw [h2, div_le_div_iff_of_pos_right hnr] at this
    exact this
  have eA : SA = ENNReal.ofReal SA.toReal := (ENNReal.ofReal_toReal hA).symm
  have eB : SB = ENNReal.ofReal SB.toReal := (ENNReal.ofReal_toReal hB).symm
  have eC : SC = ENNReal.ofReal SC.toReal := (ENNReal.ofReal_toReal hC).symm
  rw [eA, eB, eC, ← ENNReal.ofReal_mul heta, ← ENNReal.ofReal_mul h1e,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal
