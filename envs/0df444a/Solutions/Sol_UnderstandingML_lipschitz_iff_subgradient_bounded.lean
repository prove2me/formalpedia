-- Prove2me | solution 1 for UnderstandingML.lipschitz_iff_subgradient_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:41:33.064058+00:00
-- url     : https://prove2.me/submissions/97142f61-1554-4237-a8c3-28365ecc0f8f

import Definitions.Def_UnderstandingML_SGD
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

/-- Every convex function on `ℝ^d` has a subgradient at every point (supporting hyperplane to
the epigraph, via Hahn–Banach). -/
lemma exists_isSubgradient_of_convexOn {d : ℕ} {f : Vec d → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (w : Vec d) : ∃ v, IsSubgradient f w v := by
  have hcont : Continuous f := continuousOn_univ.1 (hf.continuousOn isOpen_univ)
  set s : Set (Vec d × ℝ) := {p | p.1 ∈ Set.univ ∧ f p.1 < p.2} with hs
  have hsconv : Convex ℝ s := hf.convex_strict_epigraph
  have hsopen : IsOpen s := by
    simp only [hs, Set.mem_univ, true_and]
    exact isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hx : (w, f w) ∉ s := by simp [hs]
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hsconv hsopen hx
  set c : ℝ := φ (0, 1) with hc
  set L : StrongDual ℝ (Vec d) := φ.comp (ContinuousLinearMap.inl ℝ (Vec d) ℝ) with hL
  have hdec : ∀ y t, φ (y, t) = L y + t * c := by
    intro y t
    have : ((y, t) : Vec d × ℝ) = (y, 0) + t • ((0 : Vec d), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, hL, hc]; simp
  have hcneg : c < 0 := by
    have := hφ (w, f w + 1) (by simp [hs])
    rw [hdec, hdec] at this
    linarith
  have key : ∀ y, L y + f y * c ≤ L w + f w * c := by
    intro y
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hpos : 0 < ε / (-c) := div_pos hε (by linarith)
    have := hφ (y, f y + ε / (-c)) (by simp only [hs, Set.mem_ofPred_eq, Set.mem_univ, true_and]; linarith)
    rw [hdec, hdec] at this
    have hc0 : c ≠ 0 := hcneg.ne
    have e : (f y + ε / (-c)) * c = f y * c - ε := by field_simp; ring
    linarith
  refine ⟨(InnerProductSpace.toDual ℝ (Vec d)).symm ((-c)⁻¹ • L), fun u => ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have := key u
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_sub]
  have hc' : 0 < -c := by linarith
  have : (-c)⁻¹ * (L u - L w) ≤ f u - f w := by
    rw [inv_mul_le_iff₀ hc']; nlinarith
  linarith

/-- A subgradient of a `ρ`-Lipschitz function has norm at most `ρ`. -/
lemma norm_le_of_isSubgradient_of_lipschitz {d : ℕ} {f : Vec d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlip : ∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) {w v : Vec d} (hv : IsSubgradient f w v) :
    ‖v‖ ≤ ρ := by
  have h1 := hv (w + v)
  have h2 := hlip (w + v) w
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1 h2
  have h3 : f (w + v) - f w ≤ ρ * ‖v‖ := le_trans (le_abs_self _) h2
  have h4 : ‖v‖ ^ 2 ≤ ρ * ‖v‖ := by linarith
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]; exact hρ
  · nlinarith

theorem solution {d : ℕ} (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) ↔ ∀ w v, IsSubgradient f w v → ‖v‖ ≤ ρ := by
  refine ⟨fun hlip w v hv => norm_le_of_isSubgradient_of_lipschitz hρ hlip hv, fun h u v => ?_⟩
  -- lower bound through a subgradient at `x`
  have lower : ∀ x y, f y - f x ≤ ρ * ‖x - y‖ := by
    intro x y
    obtain ⟨s, hs⟩ := exists_isSubgradient_of_convexOn hf y
    have h1 := hs x
    have h2 : |⟪x - y, s⟫_ℝ| ≤ ‖x - y‖ * ‖s‖ := abs_real_inner_le_norm _ _
    have h3 := h y s hs
    have h4 : ‖x - y‖ * ‖s‖ ≤ ‖x - y‖ * ρ := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have := neg_abs_le ⟪x - y, s⟫_ℝ
    nlinarith
  refine abs_sub_le_iff.2 ⟨?_, lower u v⟩
  have := lower v u
  rwa [norm_sub_rev] at this
