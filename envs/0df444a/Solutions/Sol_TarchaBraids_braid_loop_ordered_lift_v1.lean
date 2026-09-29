-- Prove2me | solution 1 for TarchaBraids.braid_loop_ordered_lift_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T21:50:25.042951+00:00
-- url     : https://prove2.me/submissions/535ab273-28dd-4b0a-ac5f-d25657771abf

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Theorems.Thm_BraidsLinksMCG_prop_1_1_covering

open BraidsLinksMCG unitInterval

theorem solution (n : ℕ)
    (γ : Path (baseUnordered n) (baseUnordered n)) :
    ∃ Γ : C(I, OrderedConfig n),
      (configProj n : OrderedConfig n → UnorderedConfig n) ∘ Γ = γ ∧
      Γ 0 = baseOrdered n ∧
      ∃ g : Equiv.Perm (Fin n), (Γ 1).1 = (baseOrdered n).1 ∘ g := by
  have h0 : γ 0 = configProj n (baseOrdered n) := by
    simpa [baseUnordered, configProj] using γ.source
  obtain ⟨Γ, hΓ, hΓ0⟩ :=
    (BraidsLinksMCG.prop_1_1_covering n).1.exists_path_lifts
      γ (baseOrdered n) h0
  refine ⟨Γ, hΓ, hΓ0, ?_⟩
  have h1 : configProj n (Γ 1) = baseUnordered n := by
    calc
      configProj n (Γ 1) = γ 1 := congr_fun hΓ 1
      _ = baseUnordered n := γ.target
  have hq :
      Quotient.mk (configSetoid n) (baseOrdered n) =
        Quotient.mk (configSetoid n) (Γ 1) := by
    simpa [baseUnordered, configProj] using h1.symm
  have hrel := Quotient.eq.mp hq
  change ∃ g : Equiv.Perm (Fin n),
      (Γ 1).1 = (baseOrdered n).1 ∘ g at hrel
  exact hrel
