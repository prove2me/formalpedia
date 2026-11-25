-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.exists_finite_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:48.60264+00:00
-- url     : https://prove2.me/submissions/8d2efd7e-611a-4702-91be-e5665249edbe

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem
import Theorems.Thm_PositivityTheory_ThKH_Locrep_linearIndependent_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (K : ℕ → Subgroup G) (hanti : Antitone K) (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U)
    (f : G → V) (h1 : f 1 = 0) (hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun g => l (f g)) :
    ∃ n, ∃ s : Finset V, ∀ k ∈ K n, f k ∈ Submodule.span ℂ (s : Set V) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc hc' using hne
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset V, ∀ n, T (n + 1) = insert (f (c n (T n))) (T n) :=
    ⟨fun n => Nat.rec ∅ (fun n t => insert (f (c n t)) t) n, fun _ => rfl⟩
  have hli : LinearIndependent ℂ fun n => f (c n (T n)) := by
    refine linearIndependent_of_notMem (fun n => f (c n (T n))) (fun n => (T n : Set V)) (fun m n hmn => ?_)
      fun n => hc' n (T n)
    beta_reduce
    induction n, hmn using Nat.le_induction with
    | base => rw [Nat.succ_eq_add_one, hT]; exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
    | succ n _ ih => rw [hT]; exact Finset.mem_coe.2 (Finset.mem_insert_of_mem ih)
  obtain ⟨l, hl⟩ := LinearMap.exists_extend ((Module.Basis.span hli).constr ℂ fun _ => (1 : ℂ))
  have hl1 : ∀ n, l (f (c n (T n))) = 1 := fun n => by
    have := congrArg (fun L => L (Module.Basis.span hli n)) hl
    simp only [Module.Basis.constr_basis] at this
    simpa [Module.Basis.span_apply] using this
  have hU : {g | l (f g) ≠ 1} ∈ 𝓝 (1 : G) :=
    (isOpen_ne_fun (hcont l) continuous_const).mem_nhds (by simp [h1])
  obtain ⟨n, hn⟩ := hbasis _ hU
  exact hn (hc n (T n)) (hl1 n)
end PositivityTheory.ThKH.Locrep
