-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_CommonEigenvectorInInvariantSubmodule_exists_common_eigenvector__427db1b2b1fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:01.131744+00:00
-- url     : https://prove2.me/submissions/8a31e137-8641-43e8-995f-1a538db5312e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonEigenvectorBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CommonEigenvectorInInvariantSubmodule
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ {k : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module k V] [FiniteDimensional k V] (f : ι → Module.End k V),
    (∀ (a b : ι), Commute (f a) (f b)) →
      ∀ (W : Submodule k V),
        W ≠ ⊥ →
          (∀ (i : ι), ∀ v ∈ W, (f i : V → V) v ∈ W) →
            ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ (i : ι), ∃ (μ : k), (f i : V → V) v = μ • v := by
  intro k V ι _ _ _ _ _ f hcomm W
  induction hn : Module.finrank k W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  intro hW hinv
  by_cases hs : ∀ i, ∃ μ : k, ∀ v ∈ W, f i v = μ • v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨v, hv, hv0, fun i => (hs i).imp fun μ h => h v hv⟩
  · push Not at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f i).restrict (hinv i))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : f i (w : V) = μ • (w : V) := by
      have := congrArg Subtype.val hw.apply_eq_smul
      simpa using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hmem : ∀ v, v ∈ W ⊓ Module.End.eigenspace (f i) μ ↔ v ∈ W ∧ f i v = μ • v := by
      intro v
      rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    have hne : W ⊓ Module.End.eigenspace (f i) μ ≠ ⊥ := by
      intro h
      have : (w : V) ∈ W ⊓ Module.End.eigenspace (f i) μ := (hmem _).2 ⟨w.2, hw1⟩
      rw [h] at this
      exact hw0 ((Submodule.mem_bot k).1 this)
    have hlt : W ⊓ Module.End.eigenspace (f i) μ < W := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      obtain ⟨v, hv, hv'⟩ := hi μ
      have : v ∈ W ⊓ Module.End.eigenspace (f i) μ := by rw [h]; exact hv
      exact hv' ((hmem v).1 this).2
    have hinv' : ∀ (j : ι), ∀ v ∈ W ⊓ Module.End.eigenspace (f i) μ,
        (f j : V → V) v ∈ W ⊓ Module.End.eigenspace (f i) μ := by
      intro j v hv
      obtain ⟨hvW, hvμ⟩ := (hmem v).1 hv
      refine (hmem _).2 ⟨hinv j v hvW, ?_⟩
      have hc : (f i * f j) v = (f j * f i) v := by rw [(hcomm i j).eq]
      simp only [Module.End.mul_apply] at hc
      rw [hc, hvμ, map_smul]
    obtain ⟨v, hv, hv0, hv'⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hinv'
    exact ⟨v, (Submodule.mem_inf.1 hv).1, hv0, hv'⟩
end UpperTheory.Reformulated.B.CommonEigenvectorInInvariantSubmodule
