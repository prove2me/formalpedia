-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.flow_Zb_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:03.804269+00:00
-- url     : https://prove2.me/submissions/dfcbbe89-7ad0-4949-ac9a-28b530005235

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (u : Fin 2 → Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
theorem _root_.solution (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) (s : X.Ψ → ℝ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) (X.Zb u b y) = X.Zb u b (X.flow (u 0) (cR X s) y) := by
  funext τ
  obtain ⟨W, hW⟩ : ∃ W : Fin 2 → Fin r → ℂ,
      W = fun k j => ∑ l, τ.1 (X.Gm j l) * conj (τ.1 (u k l)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin 2 → Fin r → ℂ, V = fun i a => τ.1 (u i a) := ⟨_, rfl⟩

  have hk : ∀ i k : Fin 2, ∑ j, W k j * V i j = 0 := by
    intro i k
    have h := congrArg τ.1 (hu i k)
    simp only [herm, map_sum, map_mul, emb_cc, map_zero] at h
    rw [← h, hW, hV]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  set α : ℂ := I * X.c τ * cR X s τ
  set γ : ℂ := I * X.c τ
  let A : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => α * V 0 a * W 0 j
  let B : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => γ * ∑ i, ∑ k, b τ i k * V i a * W k j
  have hF : X.flowMat (u 0) τ (cR X s τ) = 1 - A := by
    ext a j
    simp only [Data.flowMat, A, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, α]
  have hZ : X.zmat u b τ = 1 - B := by
    ext a j
    simp only [Data.zmat, B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, γ,
      Data.emb]
  have hAB : A * B = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, α * V 0 a * W 0 m * (γ * ∑ i, ∑ k, b τ i k * V i m * W k j)
        = ∑ i, ∑ k, (α * V 0 a * γ * b τ i k * W k j) * ∑ m, W 0 m * V i m := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have hBA : B * A = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, γ * (∑ i, ∑ k, b τ i k * V i a * W k m) * (α * V 0 m * W 0 j)
        = ∑ i, ∑ k, (γ * b τ i k * V i a * α * W 0 j) * ∑ m, W k m * V 0 m := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have key : X.flowMat (u 0) τ (cR X s τ) * X.zmat u b τ =
      X.zmat u b τ * X.flowMat (u 0) τ (cR X s τ) := by
    rw [hF, hZ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAB, hBA]
    abel
  show X.flowMat (u 0) τ (cR X s τ) * (X.zmat u b τ * mat y τ) =
    X.zmat u b τ * (X.flowMat (u 0) τ (cR X s τ) * mat y τ)
  rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
