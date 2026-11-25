-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.eq_top_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:15.408887+00:00
-- url     : https://prove2.me/submissions/636f6228-2c56-4c7a-bf91-c5970a892d9d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_forall_fiber


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {p : X → Y} (hp : Continuous p) (W : Submodule ℂ (SC X))
    (hW : FiberStable p W)
    (hfib : ∀ (y : Y) (D : Distr X), (∀ w ∈ W, D w = 0) → SupportedIn D (p ⁻¹' {y}) → D = 0) :
    W = ⊤ := by
  classical
  rw [eq_top_iff]
  intro g _
  let W' : Submodule ℂ (X → ℂ) := W.map (SC X).subtype
  have hmem : (g : X → ℂ) ∈ W' := by
    refine mem_of_forall_fiber (U := univ) (C := univ) isClosed_univ hp ?_ ?_ ⟨g.2, subset_univ _⟩ ?_
    · rintro f ⟨-, hf0⟩
      have : f = 0 := funext fun x => hf0 x (mem_univ x)
      rw [this]
      exact W'.zero_mem
    · rintro V hV w ⟨w0, hw0, rfl⟩
      exact ⟨mulInd (p ⁻¹' V) (hV.preimage hp) w0, hW V hV (hV.preimage hp) w0 hw0, rfl⟩
    · intro y
      let K : Submodule ℂ (SC X) := (vanishingOn (p ⁻¹' {y})).comap (SC X).subtype
      have hgM : g ∈ W ⊔ K := by
        by_contra hg
        obtain ⟨D, hDg, hDM⟩ := Submodule.exists_le_ker_of_notMem hg
        have hD0 : D = 0 := by
          refine hfib y D (fun w hw => hDM (Submodule.mem_sup_left hw)) ?_
          intro f hf
          refine hDM (Submodule.mem_sup_right ?_)
          intro x hx
          by_contra hfx
          exact hf hfx hx
        exact hDg (by rw [hD0, LinearMap.zero_apply])
      obtain ⟨w, hw, k, hk, hwk⟩ := Submodule.mem_sup.1 hgM
      refine Submodule.mem_sup.2 ⟨(w : X → ℂ), ⟨w, hw, rfl⟩, (k : X → ℂ),
        ⟨⟨k.2, subset_univ _⟩, fun x hx => hk x hx.2⟩, ?_⟩
      rw [← hwk]
      rfl
  obtain ⟨w, hw, hwg⟩ := hmem
  have : w = g := Subtype.ext hwg
  exact this ▸ hw
end PositivityTheory.PfBern.Loc
