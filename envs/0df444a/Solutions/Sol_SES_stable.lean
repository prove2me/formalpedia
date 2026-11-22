-- Prove2me | solution 1 for SES.stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:11.945855+00:00
-- url     : https://prove2.me/submissions/635c0630-03c4-4443-8f03-1e97fc23b1da

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic
import Theorems.Thm_GES_exists_enabling
import Theorems.Thm_SES_exists_least_enabling


set_option autoImplicit true
open ConfFamily
variable {L : Type*}
open GES
namespace SES
theorem _root_.solution (S : SES L) : Stable S.toFamily := by
  intro T z hne hT hz hsub
  obtain ⟨x₀, hx₀⟩ := hne
  have hsx₀ : ⋂₀ T ⊆ x₀ := fun _ hw => Set.mem_sInter.mp hw x₀ hx₀
  have hx₀z : x₀ ⊆ z := hsub x₀ hx₀
  refine ⟨fun X hX => hz.1 X (hX.trans (hsx₀.trans hx₀z)), ?_⟩
  have key : ∀ n e, e ∈ ⋂₀ T → S.toGES.rank x₀ e = n →
      ∃ m, e ∈ S.toGES.secApprox (⋂₀ T) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro e he rfl
      have hex₀ : e ∈ x₀ := hsx₀ he
      obtain ⟨k, hk⟩ : ∃ k, S.toGES.rank x₀ e = k + 1 := by
        have : S.toGES.rank x₀ e ≠ 0 := by
          intro h0
          have hmem := rank_mem ((hT x₀ hx₀).2 e hex₀)
          rw [h0] at hmem
          exact hmem
        exact ⟨S.toGES.rank x₀ e - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem ((hT x₀ hx₀).2 e hex₀)
      have hXz : (↑X : Set S.Event) ⊆ z := (hXsub.trans (secApprox_subset k)).trans hx₀z
      obtain ⟨M, hMen, hMX, hMleast⟩ :=
        SES.exists_least_enabling hz hXen hXz (hx₀z hex₀)
      have hMint : (↑M : Set S.Event) ⊆ ⋂₀ T := fun g hg => Set.mem_sInter.mpr fun x hx => by
        obtain ⟨Y, hYen, hYx⟩ :=
          exists_enabling (hT x hx) (Set.mem_sInter.mp he x hx)
        exact hYx (hMleast Y hYen (hYx.trans (hsub x hx)) hg)
      obtain ⟨N, hN⟩ := exists_bound (x := ⋂₀ T) (X := M) fun g hg => by
        refine ih _ ?_ g (hMint hg) rfl
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub (hMX hg)))
      exact ⟨N + 1, he, M, hN, hMen⟩
  exact fun e he => key _ e he rfl
end SES
