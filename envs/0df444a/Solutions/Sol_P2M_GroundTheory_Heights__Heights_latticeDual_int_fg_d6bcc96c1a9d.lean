-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:24.465912+00:00
-- url     : https://prove2.me/submissions/2193ec50-063e-421c-a48c-19d0e1b074ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PDualBasisExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ((latticeDual F.lattice).restrictScalars ℤ).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let ev : (Fin (r + 1) → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ v ↦ φ ⬝ᵥ (v : Fin (r + 1) → K)
      map_add' := by
        intro φ ψ
        funext v
        simp [add_dotProduct]
      map_smul' := by
        intro c φ
        funext v
        exact smul_dotProduct c φ (v : Fin (r + 1) → K) }
  have hspan : Submodule.span K (s : Set (Fin (r + 1) → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := 𝓞 K), hs, F.span_eq]
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    have h0 : ∀ w ∈ Submodule.span K (s : Set (Fin (r + 1) → K)), φ ⬝ᵥ w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact congrFun hφ ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
    funext j
    have := h0 (Pi.single j 1) (by rw [hspan]; exact Submodule.mem_top)
    simpa using this

  let T : Submodule ℤ (s → K) :=
    LinearMap.range (LinearMap.compLeft ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ) s)
  have hle : ((latticeDual F.lattice).restrictScalars ℤ).map ev ≤ T := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ v : s, (v : Fin (r + 1) → K) ∈ F.lattice := by
      intro v
      rw [← hs]
      exact Submodule.subset_span v.2
    refine ⟨fun v ↦ (hφ v (hv v)).choose, ?_⟩
    funext v
    exact (hφ v (hv v)).choose_spec
  have : IsNoetherian ℤ T := isNoetherian_of_isNoetherianRing_of_finite ℤ T
  exact Submodule.fg_of_fg_map_injective ev hinj (isNoetherian_submodule.mp inferInstance _ hle)
end GroundTheory.Heights₂.Heights
