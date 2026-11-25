-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.form_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:06.867454+00:00
-- url     : https://prove2.me/submissions/0edfcf39-be0f-4d71-a145-79aa8f68fae0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_asAlg_apply
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_eG_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (M : GMap K σ G T EE ρE) (P0 : Pair K G) (hM : M1 T P0) :
    M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE) := by
  set A := AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y}
  have key : ∀ (d : MonoidAlgebra K G) (y : M.VK),
      M.io (M.j (M.rhoK.asAlgebraHom d (M.rhoK.asAlgebraHom (eps P0) y))) ∈ A := by
    intro d y
    have hs : ∀ g, d.coeff g • M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y) =
        M.rhoK g (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y)) := fun g => by
      rw [map_smul, map_smul]
    rw [asAlg_apply, Finset.sum_congr rfl (fun g _ => hs g), map_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun g _ => AddSubgroup.subset_closure ?_
    refine ⟨g, M.io (M.j (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y))), ⟨d.coeff g • y, rfl⟩, ?_⟩
    rw [M.j_eq, M.io_eq]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, a, b, h⟩ := eG_mem T P0 hM
    have hx : x = M.rhoK.asAlgebraHom (eG T) x := by rw [M.good]; rfl
    simp only [map_one, Module.End.one_apply]
    rw [hx, h, map_sum, LinearMap.sum_apply, map_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    simp only [map_mul, Module.End.mul_apply]
    exact key _ _
  · intro z hz
    let f : M.VK →+ EE := (M.io.toAddMonoidHom).comp M.j.toAddMonoidHom
    have hA : A ≤ f.range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨g, _, ⟨y, rfl⟩, rfl⟩
      refine ⟨M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y), ?_⟩
      simp [f, M.j_eq, M.io_eq]
    obtain ⟨x, rfl⟩ := hA hz
    exact ⟨x, by simp [f]⟩
end PI.Dv.HermitianFormEquivalence
