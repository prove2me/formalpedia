-- Prove2me | solution 1 for PositivityTheory.ThKF.Unit.tens_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:39.496341+00:00
-- url     : https://prove2.me/submissions/6ca6abe2-183a-4ba7-bb83-18c9bdec56e5

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Theorems.Thm_PositivityTheory_ThKF_Unit_ker_le
import Theorems.Thm_PositivityTheory_KReal_tensorIrr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
namespace PositivityTheory.ThKF.Unit
theorem _root_.solution {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤)
    (R : Submodule ℂ (⨂[ℂ] i, V i)) (hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hRP : R ≤ P)
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) :
    P ≤ R ∨ P = ⊤ := by
  let q : ∀ i, A i → Module.End ℂ (V i ⧸ K i) := fun i a => (K i).mapQ (K i) (act i a) (h2 i a)
  let π := map fun i => (K i).mkQ
  have hk := ker_le K R hR
  have := PositivityTheory.KReal.tensorIrr ι A (fun i => V i ⧸ K i) q (fun i => (rank_quotient_le _).trans (hr i))
    (fun i => Submodule.Quotient.nontrivial_iff.2 (h1 i))
    (fun i N hN => by
      rcases h3 i (N.comap (K i).mkQ) (fun x hx => by simp [(Submodule.Quotient.mk_eq_zero _).2 hx])
        (fun a x hx => hN a _ hx) with e | e
      · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
        obtain ⟨x, rfl⟩ := (K i).mkQ_surjective y
        exact (Submodule.Quotient.mk_eq_zero _).2 (e ▸ hy : x ∈ K i)
      · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
        obtain ⟨x, rfl⟩ := (K i).mkQ_surjective y
        exact (e ▸ Submodule.mem_top : x ∈ N.comap (K i).mkQ))
    (P.map π) (by
      rintro i a _ ⟨x, hx, rfl⟩
      refine ⟨_, hP i a x hx, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← map_comp, ← map_comp]
      congr 2
      funext j
      by_cases h : j = i
      · subst h; simp only [Function.update_self]; rfl
      · simp [Function.update_of_ne h])
  rcases this with e | e
  · exact Or.inl fun x hx => hk ((Submodule.eq_bot_iff _).1 e _ ⟨x, hx, rfl⟩)
  · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨y, hy, e'⟩ : π x ∈ P.map π := e ▸ Submodule.mem_top
    have : x - y ∈ P := hRP (hk (show π (x - y) = 0 by rw [map_sub, e', sub_self]))
    simpa using P.add_mem this hy
end PositivityTheory.ThKF.Unit
