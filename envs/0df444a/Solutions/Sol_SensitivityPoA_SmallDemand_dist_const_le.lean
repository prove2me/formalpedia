-- Prove2me | solution 1 for SensitivityPoA.SmallDemand.dist_const_le
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-21T16:24:09.594775+00:00
-- url     : https://prove2.me/submissions/9a7c7a49-be68-451c-ae22-923e27dab37a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

set_option autoImplicit false

open SensitivityPoA.SmallDemand KellyStochasticNetworks

theorem solution : ¬ (∀ {N : Network} (τ : Fin N.J → ℝ → ℝ) (hτ : ∀ j, IsCostFn (τ j))
    (b Mτ : ℝ) (hLip : ∀ j, LipOnIcc (τ j) b Mτ)
    (d : Fin N.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand d) (hTb : totalDemand d ≤ b),
    gameDist (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N)
        (demandNormalize (totalDemand d) (⟨τ, d⟩ : Game N)) =
      sSup ((fun p : Fin N.J × ℝ => |τ p.1 (totalDemand d * p.2) - τ p.1 0|) ''
        (Set.univ ×ˢ Set.Icc 0 1)) ∧
    sSup ((fun p : Fin N.J × ℝ => |τ p.1 (totalDemand d * p.2) - τ p.1 0|) ''
        (Set.univ ×ˢ Set.Icc 0 1)) = ‖fun j => τ j (totalDemand d) - τ j 0‖ ∧
    ‖fun j => τ j (totalDemand d) - τ j 0‖ ≤ Mτ * totalDemand d) := by
  intro h
  let N : Network := ⟨0, 0, 1, fun j => j.elim0, fun r => r.elim0⟩
  have hd : totalDemand (fun _ : Fin N.Sd => (1:ℝ)) = 1 := by
    simp [totalDemand, N]
  have key := (h (N := N) (fun _ _ => 0) (fun j => j.elim0) 1 (-1) (fun j => j.elim0)
    (fun _ => 1) (fun _ => zero_le_one) (by rw [hd]; exact one_pos) (by rw [hd])).2.2
  have hn : ‖fun j : Fin N.J => ((fun (_ : Fin N.J) (_ : ℝ) => (0:ℝ)) j (totalDemand (fun _ : Fin N.Sd => (1:ℝ))) - (fun (_ : Fin N.J) (_ : ℝ) => (0:ℝ)) j 0)‖ = 0 := by
    have : Subsingleton (Fin N.J → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    exact norm_of_subsingleton _
  rw [hn, hd] at key
  norm_num at key
