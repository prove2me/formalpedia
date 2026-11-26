-- Prove2me | solution 1 for Scott1972.ContinuousLattice.inverseLimit_isInjectiveSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:37.239149+00:00
-- url     : https://prove2.me/submissions/35ea198e-9500-4b07-adef-54d5ab045cf3

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_coordinate_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_lemma_3_9
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_eq_of_continuous


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : ∀ n, IsContinuousLattice (D n)) :
    @IsInjectiveSpace.{u, u} (InverseLimit D P) (inverseLimitTopology D P) := by
  intro X Y _ _ e he f
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  letI : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  letI : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  letI : ∀ n, Preorder (D n) := stageOrder
  letI : Preorder (InverseLimit D P) := limitOrder
  let fcoord (n : ℕ) (x : X) : D n := (f x).1 n
  have hfcoord (n : ℕ) : @Continuous X (D n) _ scottTopologicalSpace (fcoord n) :=
    (inverseLimit_coordinate_continuous D P n).comp f.continuous
  let fbar (n : ℕ) : Y → D n := scottExtend e (fcoord n)
  have hfbar_cont (n : ℕ) :
      @Continuous Y (D n) _ scottTopologicalSpace (fbar n) :=
    scottExtend_continuous (hD n) e (fcoord n)
  have hfbar_compat (y : Y) (n : ℕ) :
      (P n).retr (fbar (n + 1) y) = fbar n y := by
    symm
    exact lemma_3_9 (hD n) (hD (n + 1)) (P n) e he
      (hfcoord n) (hfcoord (n + 1)) (fun x => (f x).2 n |>.symm) y
  let fbarInf (y : Y) : InverseLimit D P :=
    ⟨fun n => fbar n y, hfbar_compat y⟩
  have hfbarInf_cont :
      @Continuous Y (InverseLimit D P) _ (inverseLimitTopology D P) fbarInf := by
    change @Continuous Y (InverseLimit D P) _
      (TopologicalSpace.induced (Subtype.val : InverseLimit D P → ∀ n, D n)
        (@Pi.topologicalSpace ℕ D (fun _ => scottTopologicalSpace))) fbarInf
    rw [continuous_induced_rng]
    exact continuous_pi hfbar_cont
  refine ⟨⟨fbarInf, hfbarInf_cont⟩, fun x => ?_⟩
  apply Subtype.ext
  funext n
  exact scottExtend_eq_of_continuous (hD n) e he (fcoord n) (hfcoord n) x
end Scott1972.ContinuousLattice
