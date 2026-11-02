-- Prove2me | solution 1 for ProbEffIS.GE.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:10:38.64838+00:00
-- url     : https://prove2.me/submissions/8ebd2020-d80c-47a2-85dc-b515d4187c84

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs
import Theorems.Thm_ProbEffIS_GE_halfspace_bound

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.T2

variable {d : ℕ}

lemma rate_ne_bot (μ : Rd d → EReal) (hμ0 : μ 0 ≠ ⊤) (y : Rd d) (hy : rate μ y ≠ ⊤) :
    rate μ y ≠ ⊥ := by
  have hμ0b : μ 0 ≠ ⊥ := by
    intro h
    apply hy
    refine top_le_iff.1 ?_
    have := le_iSup (fun x => ((inner ℝ x y : ℝ) : EReal) - μ x) 0
    simp only [h, EReal.coe_sub_bot] at this
    exact this
  have h := le_iSup (fun x => ((inner ℝ x y : ℝ) : EReal) - μ x) 0
  intro hb
  rw [show rate μ y = ⨆ x, ((inner ℝ x y : ℝ) : EReal) - μ x from rfl] at hb
  rw [hb, le_bot_iff] at h
  rw [← EReal.coe_toReal hμ0 hμ0b, ← EReal.coe_sub] at h
  exact EReal.coe_ne_bot _ h

/-- Convexity of the rate function on its effective domain. -/
lemma rate_comb (μ : Rd d → EReal) (y z : Rd d) (hy : rate μ y ≠ ⊤) (hz : rate μ z ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    rate μ (a • y + b • z) ≤ ((a * (rate μ y).toReal + b * (rate μ z).toReal : ℝ) : EReal) := by
  have hnb : ∀ x, μ x ≠ ⊥ := by
    intro x hx
    apply hy
    refine top_le_iff.1 ?_
    have := le_iSup (fun w => ((inner ℝ w y : ℝ) : EReal) - μ w) x
    simp only [hx, EReal.coe_sub_bot] at this
    exact this
  refine iSup_le fun x => ?_
  by_cases hxt : μ x = ⊤
  · rw [hxt, EReal.sub_top]; exact bot_le
  have hμx : μ x = ((μ x).toReal : EReal) := (EReal.coe_toReal hxt (hnb x)).symm
  have hyb : rate μ y ≠ ⊥ := ne_bot_of_le_ne_bot (by
      rw [hμx, ← EReal.coe_sub]; exact EReal.coe_ne_bot _)
    (le_iSup (fun w => ((inner ℝ w y : ℝ) : EReal) - μ w) x)
  have hzb : rate μ z ≠ ⊥ := ne_bot_of_le_ne_bot (by
      rw [hμx, ← EReal.coe_sub]; exact EReal.coe_ne_bot _)
    (le_iSup (fun w => ((inner ℝ w z : ℝ) : EReal) - μ w) x)
  have h1 : ((inner ℝ x y - (μ x).toReal : ℝ) : EReal) ≤ ((rate μ y).toReal : EReal) := by
    rw [EReal.coe_toReal hy hyb, EReal.coe_sub, ← hμx]
    exact le_iSup (fun w => ((inner ℝ w y : ℝ) : EReal) - μ w) x
  have h2 : ((inner ℝ x z - (μ x).toReal : ℝ) : EReal) ≤ ((rate μ z).toReal : EReal) := by
    rw [EReal.coe_toReal hz hzb, EReal.coe_sub, ← hμx]
    exact le_iSup (fun w => ((inner ℝ w z : ℝ) : EReal) - μ w) x
  rw [EReal.coe_le_coe_iff] at h1 h2
  rw [hμx, ← EReal.coe_sub, EReal.coe_le_coe_iff, inner_add_right, inner_smul_right,
    inner_smul_right]
  have : (μ x).toReal = a * (μ x).toReal + b * (μ x).toReal := by
    rw [← add_mul, hab, one_mul]
  nlinarith

lemma rate_convexOn (μ : Rd d → EReal) (hμ0 : μ 0 ≠ ⊤) :
    ConvexOn ℝ (dom (rate μ)) (fun y => (rate μ y).toReal) := by
  refine ⟨fun y hy z hz a b ha hb hab => ?_, fun y hy z hz a b ha hb hab => ?_⟩
  · show rate μ (a • y + b • z) < ⊤
    exact lt_of_le_of_lt (rate_comb μ y z hy.ne hz.ne a b ha hb hab) (EReal.coe_lt_top _)
  · have h := rate_comb μ y z hy.ne hz.ne a b ha hb hab
    have hne : rate μ (a • y + b • z) ≠ ⊤ := (lt_of_le_of_lt h (EReal.coe_lt_top _)).ne
    have := EReal.toReal_le_toReal h (rate_ne_bot μ hμ0 _ hne) (EReal.coe_ne_top _)
    rw [EReal.toReal_coe] at this
    exact this

end ProbEffIS.GE.T2

open ProbEffIS.GE ProbEffIS.GE.T2 in
theorem solution {d r : ℕ} (ν : ℝ → Measure (Rd d))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s) :
    ∃ i : Fin r, rateOn μ R = rate μ (a i) ∧
      ∀ j : Fin r, rate μ (a i) ≤ rate μ (a j) := by
  obtain ⟨y0, hy0⟩ := h2.meets
  have hy0R : y0 ∈ R := interior_subset hy0.1
  obtain ⟨j0, -⟩ : ∃ j, y0 ∈ halfspace (s j) (a j) := by simpa using hA.cover hy0R
  have : Nonempty (Fin r) := ⟨j0⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun j => rate μ (a j))
    Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ ?_, fun j => hi j (Finset.mem_univ j)⟩
  · have hμ0 : μ 0 ≠ ⊤ := (interior_subset h1.zero_mem : (0 : Rd d) ∈ dom μ).ne
    have hai := hA.mem_interior_dom_rate i
    have hai_top : rate μ (a i) ≠ ⊤ := (interior_subset hai : a i ∈ dom (rate μ)).ne
    have hcont : ContinuousAt (fun y => (rate μ y).toReal) (a i) :=
      (rate_convexOn μ hμ0).continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hai)
    rw [← EReal.coe_toReal hai_top (rate_ne_bot μ hμ0 _ hai_top)]
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    have hU : (fun y => (rate μ y).toReal) ⁻¹' Set.Iio z ∩ interior (dom (rate μ)) ∈ 𝓝 (a i) :=
      Filter.inter_mem (hcont.preimage_mem_nhds (Iio_mem_nhds hz)) (isOpen_interior.mem_nhds hai)
    have hcl : a i ∈ closure R := frontier_subset_closure (hA.mem_frontier i)
    obtain ⟨y, ⟨hyz, hyD⟩, hyR⟩ := mem_closure_iff_nhds.1 hcl _ hU
    have hyt : rate μ y ≠ ⊤ := (interior_subset hyD : y ∈ dom (rate μ)).ne
    calc rateOn μ R ≤ rate μ y := iInf₂_le y hyR
      _ = ((rate μ y).toReal : EReal) := (EReal.coe_toReal hyt (rate_ne_bot μ hμ0 _ hyt)).symm
      _ ≤ (z : EReal) := EReal.coe_le_coe_iff.2 (le_of_lt hyz)
  · refine le_iInf₂ fun y hy => ?_
    obtain ⟨j, hj⟩ : ∃ j, y ∈ halfspace (s j) (a j) := by simpa using hA.cover hy
    exact (hi j (Finset.mem_univ _)).trans
      ((halfspace_bound ν μ h1 (s j) (a j) (hA.tilt_mem j) (hA.grad_eq j)).2 y hj)
