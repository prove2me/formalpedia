-- Prove2me | solution 1 for ProbEffIS.GE.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:20:03.247197+00:00
-- url     : https://prove2.me/submissions/07723934-a9f5-4979-9e6d-c164118931dc

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs
import Theorems.Thm_ProbEffIS_GE_halfspace_bound
import Theorems.Thm_ProbEffIS_GE_theorem_2
import Theorems.Thm_ProbEffIS_GE_ge_upper_bound
import Theorems.Thm_ProbEffIS_GE_ge_lower_bound

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.T1

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


end ProbEffIS.GE.T1

open ProbEffIS.GE ProbEffIS.GE.T1 in
theorem solution {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    -(rateOn μ (interior B)) ≤
      liminf (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ∧
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop ≤
        -(rateOn μ (closure B)) ∧
    (Assumption2 μ B → ∀ (r : ℕ) (a s : Fin r → Rd d), IsDominatingSet μ B a s →
      Tendsto (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B}))
        atTop (𝓝 (-(rateOn μ B)))) := by
  have hL := ge_lower_bound ν hν μ h1 B hB
  have hU := ge_upper_bound ν hν μ h1 B hB
  refine ⟨hL, hU, fun h2 r a s hA => ?_⟩
  obtain ⟨i, hiR, hmin⟩ := theorem_2 ν μ h1 B h2 a s hA
  -- the rate over the closure is at least `I(a_i)`
  have hcl : rate μ (a i) ≤ rateOn μ (closure B) := by
    have hclosed : IsClosed (⋃ j, halfspace (s j) (a j)) :=
      isClosed_iUnion_of_finite fun j => isClosed_le continuous_const
        (continuous_const.inner (continuous_id.sub continuous_const))
    have hsub : closure B ⊆ ⋃ j, halfspace (s j) (a j) := closure_minimal hA.cover hclosed
    refine le_iInf₂ fun y hy => ?_
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hsub hy)
    exact (hmin j).trans
      ((halfspace_bound ν μ h1 (s j) (a j) (hA.tilt_mem j) (hA.grad_eq j)).2 y hj)
  -- the rate over the interior is at most `I(a_i)`
  have hint : rateOn μ (interior B) ≤ rate μ (a i) := by
    have hμ0 : μ 0 ≠ ⊤ := (interior_subset h1.zero_mem : (0 : Rd d) ∈ dom μ).ne
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
    have hcl : a i ∈ closure (interior B) := by
      rw [← h2.closure_eq]; exact frontier_subset_closure (hA.mem_frontier i)
    obtain ⟨y, ⟨hyz, hyD⟩, hyR⟩ := mem_closure_iff_nhds.1 hcl _ hU
    have hyt : rate μ y ≠ ⊤ := (interior_subset hyD : y ∈ dom (rate μ)).ne
    calc rateOn μ (interior B) ≤ rate μ y := iInf₂_le y hyR
      _ = ((rate μ y).toReal : EReal) := (EReal.coe_toReal hyt (rate_ne_bot μ hμ0 _ hyt)).symm
      _ ≤ (z : EReal) := EReal.coe_le_coe_iff.2 (le_of_lt hyz)
  have h_int_B : rateOn μ B ≤ rateOn μ (interior B) :=
    le_iInf₂ fun y hy => iInf₂_le y (interior_subset hy)
  have h_B_cl : rateOn μ (closure B) ≤ rateOn μ B :=
    le_iInf₂ fun y hy => iInf₂_le y (subset_closure hy)
  have e1 : rateOn μ (interior B) = rateOn μ B := le_antisymm (hint.trans (hcl.trans h_B_cl)) h_int_B
  have e2 : rateOn μ (closure B) = rateOn μ B := le_antisymm h_B_cl (h_int_B.trans (hint.trans hcl))
  rw [e1] at hL
  rw [e2] at hU
  exact tendsto_of_le_liminf_of_limsup_le hL hU
