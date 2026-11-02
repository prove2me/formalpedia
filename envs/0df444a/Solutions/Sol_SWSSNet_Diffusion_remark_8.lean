-- Prove2me | solution 1 for SWSSNet.Diffusion.remark_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:53:06.991279+00:00
-- url     : https://prove2.me/submissions/c6e0f5be-eba1-4c9b-b635-938c65bc6272

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process
import Theorems.Thm_SWSSNet_Diffusion_proposition_2
import Theorems.Thm_SWSSNet_Diffusion_theorem_3
import Theorems.Thm_SWSSNet_Diffusion_theorem_4

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSRemark8Aux

open SWSSNet.Diffusion

/-- Shifting a strong solution by a constant vector `c`, when the drifts are related by
`b₂(y + c) = b₁(y)`. -/
theorem strong_shift {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
    (b₁ b₂ : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (σ : Matrix (Fin d) (Fin d) ℝ)
    (c : EthierKurtz.SDEState d) (hb : ∀ y, b₂ (y + c) = b₁ y)
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState d) (x : EthierKurtz.SDEState d)
    (hX : UnifErgHW.Diffusion.IsStrongSolution Pr b₁ σ B X x) :
    UnifErgHW.Diffusion.IsStrongSolution Pr b₂ σ B (fun t ω => X t ω + c) (x + c) := by
  obtain ⟨⟨hcont, heq⟩, hmeas, hF⟩ := hX
  refine ⟨⟨fun ω => (hcont ω).add continuous_const, fun ω t => ?_⟩, fun t => (hmeas t).add_const c,
    fun t => ?_⟩
  · have hfun : (fun s : ℝ => b₂ (X (Real.toNNReal s) ω + c)) =
        fun s : ℝ => b₁ (X (Real.toNNReal s) ω) := funext fun s => hb _
    simp only [hfun]
    rw [heq ω t]
    abel
  · obtain ⟨F, hFm, hFae⟩ := hF t
    refine ⟨fun w => F w + c, hFm.add_const c, ?_⟩
    filter_upwards [hFae] with ω hω
    rw [hω]

/-- A pool forces a class: the CRP column sums equal `1`. -/
theorem exists_class {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) : Nonempty (Fin I) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := N.xi_crp.2.2.2.1 ĵ
  simp at this

/-- Every pool has a neighbouring class in the tree. -/
theorem exists_neighbor {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) : ∃ î, N.adj î ĵ := by
  obtain ⟨i0⟩ := exists_class N ĵ
  obtain ⟨w⟩ := N.isTree.isConnected.preconnected (Sum.inr ĵ) (Sum.inl i0)
  cases w with
  | cons h _ =>
    rename_i v
    unfold bipGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨i, j, h1, _, _⟩ | ⟨i, j, h1, h2, h3⟩
    · cases h1
    · cases h2
      exact ⟨i, h3⟩

/-- `⟨e, B₁⁻¹ p⟩ > 0` for a positive vector `p`. -/
theorem denom_pos {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ)
    (hp : IsPosProb p) : 0 < ∑ i, ((B1 N ĵ)⁻¹ *ᵥ p) i := by
  have hpos := (theorem_3 N ĵ).2
  obtain ⟨i0⟩ := exists_class N ĵ
  have hswap : ∑ i, ((B1 N ĵ)⁻¹ *ᵥ p) i = ∑ k, (∑ i, (B1 N ĵ)⁻¹ i k) * p k := by
    simp only [mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_pos (fun k _ => mul_pos (hpos k) (hp.1 k)) ⟨i0, Finset.mem_univ _⟩

/-- `B₁` is invertible. -/
theorem B1_isUnit {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) : IsUnit (B1 N ĵ).det := by
  by_contra h
  have h0 := Matrix.nonsing_inv_apply_not_isUnit (B1 N ĵ) h
  obtain ⟨i0⟩ := exists_class N ĵ
  have := (theorem_3 N ĵ).2 i0
  simp [h0] at this

end SWSSRemark8Aux

open SWSSNet.Diffusion SWSSRemark8Aux

theorem solution {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    let ζ : EthierKurtz.SDEState I := WithLp.toLp 2 ((B1 N ĵ)⁻¹ *ᵥ (hvec N + swss N p • p))
    (∑ i, ζ i = 0) ∧
    (∀ (u : (Fin I → ℝ) × (Fin J → ℝ)) (x : EthierKurtz.SDEState I), IsControlValue u →
      driftH N (hvec N) u (x + ζ) = driftH N (-(swss N p) • p) u x) ∧
    ∀ (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)), IsMarkovControl v →
      ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (B X : ℝ≥0 → Ω → EthierKurtz.SDEState I) (x : EthierKurtz.SDEState I),
        EthierKurtz.IsStandardBrownian Pr B →
        UnifErgHW.Diffusion.IsStrongSolution Pr (markovDrift N (-(swss N p) • p) v) (Sigma N) B X x →
        UnifErgHW.Diffusion.IsStrongSolution Pr (markovDrift N (hvec N) (fun y => v (y - ζ)))
          (Sigma N) B (fun t ω => X t ω + ζ) (x + ζ) := by
  intro ζ
  set ϑ := swss N p with hϑ
  set Binv := (B1 N ĵ)⁻¹ with hBinv
  have hζi : ∀ i, ζ i = (Binv *ᵥ (hvec N + ϑ • p)) i := fun i => rfl
  -- (i) ⟨e, ζ⟩ = 0
  have hsum : ∑ i, ζ i = 0 := by
    have h4 := theorem_4 N ĵ p hp
    have hd := denom_pos N ĵ p hp
    simp only [hζi, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hBinv, hϑ, h4]
    field_simp
    ring
  -- (ii) the drift identity
  have hBB : B1 N ĵ *ᵥ (Binv *ᵥ (hvec N + ϑ • p)) = hvec N + ϑ • p := by
    rw [mulVec_mulVec, hBinv, Matrix.mul_nonsing_inv _ (B1_isUnit N ĵ), one_mulVec]
  obtain ⟨î, hedge⟩ := exists_neighbor N ĵ
  have hP2 := (proposition_2 N î ĵ hedge).1
  have hdrift : ∀ (u : (Fin I → ℝ) × (Fin J → ℝ)) (x : EthierKurtz.SDEState I), IsControlValue u →
      driftH N (hvec N) u (x + ζ) = driftH N (-ϑ • p) u x := by
    intro u x hu
    rw [hP2 _ u _ hu, hP2 _ u _ hu]
    have hsx : ∑ l, (x + ζ) l = ∑ l, x l := by
      simp only [PiLp.add_apply, Finset.sum_add_distrib, hsum, add_zero]
    rw [hsx]
    have hvec_eq : (fun k => (x + ζ) k - max (∑ l, x l) 0 * u.1 k) =
        (fun k => x k - max (∑ l, x l) 0 * u.1 k) + Binv *ᵥ (hvec N + ϑ • p) := by
      funext k
      simp only [PiLp.add_apply, Pi.add_apply, hζi]
      ring
    rw [hvec_eq, mulVec_add, hBB]
    congr 1
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_smul]
    ring
  refine ⟨hsum, hdrift, ?_⟩
  -- (iii) translating strong solutions
  intro v hv Ω _ Pr _ B X x _ hX
  refine strong_shift Pr _ _ (Sigma N) ζ (fun y => ?_) B X x hX
  simp only [markovDrift, add_sub_cancel_right]
  exact hdrift (v y) y (hv.2 y)
