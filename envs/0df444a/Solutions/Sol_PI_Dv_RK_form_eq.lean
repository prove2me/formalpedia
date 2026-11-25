-- Prove2me | solution 1 for PI.Dv.RK.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:58.416362+00:00
-- url     : https://prove2.me/submissions/4df8bf7f-27f5-42f0-89c0-d50f664ce3e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
variable (M : GMap K σ G T EE ρE)
namespace PI.Dv.RK
theorem _root_.solution (P0 : Pair K G)
    (hF : eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P0 * b}) :
    M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE) := by
  set Y := AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} with hY
  have hgen : ∀ (a : MonoidAlgebra K G) (w : M.VK),
      M.io (M.j (M.rhoK.asAlgebraHom a (M.rhoK.asAlgebraHom (eps P0) w))) ∈ Y := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      intro w
      apply AddSubgroup.subset_closure
      refine ⟨g, _, ⟨w, rfl⟩, ?_⟩
      rw [Representation.asAlgebraHom_of, M.j_eq, M.io_eq]
    | add a b ha hb =>
      intro w
      rw [map_add, LinearMap.add_apply, map_add, map_add]
      exact Y.add_mem (ha w) (hb w)
    | smul r a ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply, ← map_smul (M.rhoK.asAlgebraHom a),
        ← map_smul (M.rhoK.asAlgebraHom (eps P0))]
      exact ha (r • w)
  have hall : ∀ x : M.VK, M.io (M.j (M.rhoK.asAlgebraHom (eG T) x)) ∈ Y := by
    refine AddSubgroup.closure_induction (p := fun z _ => ∀ x : M.VK,
      M.io (M.j (M.rhoK.asAlgebraHom z x)) ∈ Y) ?_ ?_ ?_ ?_ hF
    · rintro z ⟨a, b, rfl⟩ x
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact hgen a _
    · intro x
      rw [map_zero, LinearMap.zero_apply, map_zero, map_zero]
      exact Y.zero_mem
    · intro x y _ _ hx hy w
      rw [map_add, LinearMap.add_apply, map_add, map_add]
      exact Y.add_mem (hx w) (hy w)
    · intro x _ hx w
      rw [map_neg, LinearMap.neg_apply, map_neg, map_neg]
      exact Y.neg_mem (hx w)
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have := hall x
    rw [M.good] at this
    simpa using this
  · intro z hz
    have hle : Y ≤ (M.io.toAddMonoidHom.comp M.j.toAddMonoidHom).range := by
      rw [hY, AddSubgroup.closure_le]
      rintro _ ⟨g, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨M.rhoK g (M.rhoK.asAlgebraHom (eps P0) w), by simp [M.j_eq, M.io_eq]⟩
    obtain ⟨x, hx⟩ := hle hz
    exact ⟨x, by simpa using hx⟩
end PI.Dv.RK
