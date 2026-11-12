-- Prove2me | solution 1 for RiskAverseConsistency.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:35:09.413765+00:00
-- url     : https://prove2.me/submissions/ff426fc5-3a4a-4437-ad12-34214ad7e126

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_EpiConvergesOn
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn

open Filter Topology QuasiHemiVI.Existence

open RiskAverseConsistency in
theorem solution {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (hZ : IsReflexive Z)
    {Z₀ : Set Z} (hZ₀_ne : Z₀.Nonempty) (hZ₀_closed : IsClosed Z₀) (hZ₀_convex : Convex ℝ Z₀)
    {Y₀ : Set Y} (hY₀_closed : IsClosed Y₀) (B : Z →ₗ[ℝ] Y)
    (hB : CompletelyContinuousOn Set.univ B) (hBZ₀ : Set.MapsTo B Z₀ Y₀)
    (h : ℕ → Y → EReal) (hlim : Y → EReal) (h_ne_bot : ∀ k, ∀ y ∈ Y₀, h k y ≠ ⊥)
    (hlim_ne_bot : ∀ y ∈ Y₀, hlim y ≠ ⊥) (hepi : EpiConvergesOn Y₀ h hlim)
    (hepiB : EpiConvergesOn Z₀ (fun k z => h k (B z)) (fun z => hlim (B z))) :
    MoscoConvergesOn Z₀ (fun k z => h k (B z)) (fun z => hlim (B z)) := by
  intro v hv
  refine ⟨?_, (hepiB v hv).2⟩
  intro u hu hw
  have hT : Tendsto (fun k => B (u k)) atTop (𝓝 (B v)) :=
    hB u v (fun _ => Set.mem_univ _) (Set.mem_univ _) hw
  exact (hepi (B v) (hBZ₀ hv)).1 (fun k => B (u k)) (fun k => hBZ₀ (hu k)) hT
