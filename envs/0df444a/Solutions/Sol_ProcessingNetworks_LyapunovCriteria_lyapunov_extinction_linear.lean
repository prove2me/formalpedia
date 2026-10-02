-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.lyapunov_extinction_linear
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:07:43.459986+00:00
-- url     : https://prove2.me/submissions/9f1679df-d0ba-4324-9246-0896ea5506ba

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace Cex53851659

open ProcessingNetworks.LyapunovCriteria

/-- One buffer, no activities, no server pools, arrival rate 1. -/
def dat : FluidEquationData 1 0 0 where
  B := 0
  Γ := 0
  m := 0
  A := 0
  b := 0
  lam := fun _ => 1

/-- `H z = -(z 0)`: Lipschitz, `H 0 = 0`, nonzero off `0`, but negative on the orthant. -/
def H : (Fin 1 → ℝ) → ℝ := fun z => -(z 0)

def Zh : ℝ → Fin 1 → ℝ := fun t _ => 1 + t

theorem H_lip : IsLipschitzOn H {z : Fin 1 → ℝ | ∀ i, 0 ≤ z i} := by
  intro B _
  refine ⟨1, ?_⟩
  have hL : LipschitzWith 1 H := by
    have : LipschitzWith 1 (fun z : Fin 1 → ℝ => z 0) := LipschitzWith.eval 0
    exact this.neg
  exact hL.lipschitzOnWith

theorem H_pos : ∀ z : Fin 1 → ℝ, z ≠ (fun _ => 0) → H z ≠ 0 := by
  intro z hz h
  apply hz
  funext i
  fin_cases i
  simp only [H, neg_eq_zero] at h
  simpa using h

theorem sol : IsFluidModelSolution dat (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) Zh := by
  refine ⟨?_, ?_, ?_, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro t _ i
    simp [Zh, dat]
  · intro t ht i
    simp only [Zh]
    linarith
  · intro t _ i
    simp
  · intro t _ j
    exact j.elim0
  · intro a b _
    exact le_rfl
  · intro s t _ _ k
    exact k.elim0

theorem drift : ∀ᵐ t, 0 ≤ t → Zh t ≠ (fun _ => 0) →
    ∀ d : ℝ, HasDerivAt (fun s => H (Zh s)) d t → d ≤ -(1 : ℝ) := by
  refine Filter.Eventually.of_forall (fun t _ _ d hd => ?_)
  have h1 : HasDerivAt (fun s => H (Zh s)) (-1) t := by
    exact ((hasDerivAt_id t).const_add 1).neg
  rw [hd.unique h1]

end Cex53851659

open MeasureTheory ProcessingNetworks.LyapunovCriteria in
theorem solution : ¬ (∀ {I : ℕ} (H : (Fin I → ℝ) → ℝ)
    (hH_lip : IsLipschitzOn H {z : Fin I → ℝ | ∀ i, 0 ≤ z i})
    (hH0 : H (fun _ => 0) = 0) (hHpos : ∀ z : Fin I → ℝ, z ≠ (fun _ => 0) → H z ≠ 0)
    {J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → Zh t ≠ (fun _ => 0) →
      ∀ d : ℝ, HasDerivAt (fun s => H (Zh s)) d t → d ≤ -ε),
    ∀ t : ℝ, H (Zh 0) / ε ≤ t → Zh t = fun _ => 0) := by
  intro h
  have key := h Cex53851659.H Cex53851659.H_lip (by simp [Cex53851659.H])
    Cex53851659.H_pos Cex53851659.dat
    (fun k _ => k.elim0) (fun j => j.elim0)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) Cex53851659.Zh Cex53851659.sol
    1 one_pos Cex53851659.drift 0 (by norm_num [Cex53851659.H, Cex53851659.Zh])
  have := congrFun key 0
  norm_num [Cex53851659.Zh] at this
