-- Prove2me | solution 1 for PositivityTheory.CW.MaximumPrincipleOneFunction.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:48.366034+00:00
-- url     : https://prove2.me/submissions/f27c7f38-6600-42db-91cf-49cab10ab183

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MaximumPrincipleOneFunction
variable {n : ℕ}
namespace PositivityTheory.CW.MaximumPrincipleOneFunction
theorem _root_.solution (hB3 : B3) (hB3g : UnitaryGroupFacts) (ε : Fin n → Bool) (r : ℕ) (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A η : ℝ)
    (g0 : Matrix (Fin n) (Fin n) ℂ)
    (hmax : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
      u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1))
    (hg0 : g0 ∈ UJset ε) (p : Fin n × Fin n) (hp : p ∈ nc ε)
    (u' : ℝ → ℝ) (d : ℝ)
    (hu' : ∀ t, HasDerivAt (fun t : ℝ => u (g0 * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t)
    (hd : HasDerivAt u' d 0)
    (v' : ℝ → ℝ) (v'' : ℝ)
    (hv' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r) (v' t) t)
    (hv'' : HasDerivAt v' v'' 0)
    (w' : ℝ → ℝ) (w'' : ℝ)
    (hw' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (w' t) t)
    (hw'' : HasDerivAt w' w'' 0) :
    d - A * v'' - η * w'' ≤ 0 := by
  obtain ⟨-, -, hmem, -, -, hX⟩ := hB3g n ε
  have hXp := hX p hp
  refine hB3 (fun t => u (g0 * NormedSpace.exp (t • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1))
    (fun t => u' t - A * v' t - η * w' t) _ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    have h0 : g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2) = g0 := by simp
    show _ ≤ u (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ (r + 1)
    rw [h0]
    exact hmax _ (hmem g0 hg0 _ hXp t)
  · intro t
    exact ((hu' t).sub ((hv' t).const_mul A)).sub ((hw' t).const_mul η)
  · exact (hd.sub (hv''.const_mul A)).sub (hw''.const_mul η)
end PositivityTheory.CW.MaximumPrincipleOneFunction
