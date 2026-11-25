-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.generatedSub_closure_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:12.275177+00:00
-- url     : https://prove2.me/submissions/e340def2-59fa-460d-be7e-386b073267e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrixAction_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrixAction_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrixAction_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hermPart_mem_lieAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hermPart_mem_lieAlgebra_var
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrix_decomp_lieAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mul_mem_unitaryJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_one_mem_unitaryJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_smul_mem_UJset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (A : Submodule ℂ H) (hA : IsClosed (A : Set H))
    (hVA : ∀ g ∈ UJset ε, ∀ v ∈ V, σ g (v : H) ∈ A) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ A := by
  let T : Submodule ℂ D :=
    { carrier := {v | ∀ g ∈ UJset ε, σ g (v : H) ∈ A}
      add_mem' := by
        intro u w hu hw g hg
        simp only [Set.mem_setOf_eq] at hu hw
        simpa using A.add_mem (hu g hg) (hw g hg)
      zero_mem' := by
        intro g hg
        simp
      smul_mem' := by
        intro c v hv g hg
        simp only [Set.mem_setOf_eq] at hv
        simpa using A.smul_mem c (hv g hg) }
  have hder : ∀ X, inG ε X → ∀ v ∈ T, actM E X v ∈ T := by
    intro X hX v hv
    have hv' : ∀ g ∈ UJset ε, σ g (v : H) ∈ A := hv
    show ∀ g ∈ UJset ε, σ g ((actM E X v : D) : H) ∈ A
    intro g hg
    have hd := hD.deriv X hX v
    have hd2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
        (σ g ((actM E X v : D) : H)) 0 :=
      ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have hval : ∀ t : ℝ, σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ∈ A := by
      intro t
      have hmul := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
      have h5 := hv' (g * NormedSpace.exp ((t : ℂ) • X)) (mul_mem_unitaryJ hg (exp_smul_mem_UJset hX t))
      rw [hmul] at h5
      exact h5
    refine hA.mem_of_tendsto hd2.tendsto_slope_zero ?_
    filter_upwards with t
    exact A.smul_of_tower_mem _ (A.sub_mem (hval _) (hval _))
  have hE : ∀ a b, ∀ v ∈ T, E a b v ∈ T := by
    intro a b v hv
    rw [← matrixAction_single E a b, matrix_decomp_lieAlgebra ε (Matrix.single a b (1 : ℂ)), matrixAction_add,
      matrixAction_smul E Complex.I, LinearMap.add_apply, LinearMap.smul_apply]
    exact T.add_mem (hder _ (hermPart_mem_lieAlgebra ε _) v hv) (T.smul_mem _ (hder _ (hermPart_mem_lieAlgebra_var ε _) v hv))
  have hGT : genSub E V ≤ T := sInf_le ⟨fun v hv =>
    (show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from fun g hg => hVA g hg v hv), hE⟩
  refine Submodule.topologicalClosure_minimal _ ?_ hA
  rintro _ ⟨v, hv, rfl⟩
  have h1 : σ 1 (v : H) ∈ A := (show ∀ g ∈ UJset ε, σ g (v : H) ∈ A from hGT hv) 1 (one_mem_unitaryJ ε)
  rw [hσ.1.1] at h1
  simpa using h1
end ReciprocityTheory.ChartRestriction.DS
