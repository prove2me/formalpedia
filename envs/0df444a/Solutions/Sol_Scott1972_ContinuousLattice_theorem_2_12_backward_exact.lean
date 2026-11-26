-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_2_12_backward_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:25.515226+00:00
-- url     : https://prove2.me/submissions/cbed9409-456d-4fdd-af60-6fb9b38ac06b

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_backward
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_orderIso
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_SpecializationLe_map
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_scott_iff


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]
namespace Scott1972.ContinuousLattice
theorem _root_.solution [τA : TopologicalSpace A] [T0Space A]
    (hA : IsInjectiveSpace.{u, u} A)
    (hspec : ∀ x y : A, SpecializationLe x y ↔ @LE.le A latticeA.toLE x y) :
    IsContinuousLattice A ∧
      (@scottTopologicalSpace A latticeA) = τA := by
  obtain ⟨E, instE, hE, ⟨h⟩⟩ := theorem_2_12_backward hA
  letI : CompleteLattice E := instE
  letI : TopologicalSpace E := @scottTopologicalSpace E instE
  letI : Preorder A := latticeA.toPreorder
  letI : Preorder E := instE.toPreorder
  let e : A ≃o E := h.toEquiv.toOrderIso
    (fun x y hxy => by
      exact specializationLe_scott_iff.mp
        (SpecializationLe.map ((hspec x y).mpr hxy) h.continuous))
    (fun x y hxy => by
      exact (hspec (h.symm x) (h.symm y)).mp
        (SpecializationLe.map (specializationLe_scott_iff.mpr hxy) h.symm.continuous))
  have hcont : IsContinuousLattice A := IsContinuousLattice.orderIso e hE
  refine ⟨hcont, ?_⟩
  have heqOrder :
      (@scottTopologicalSpace A latticeA) =
        TopologicalSpace.induced (e : A → E) (@scottTopologicalSpace E instE) := by
    letI : TopologicalSpace A := @scottTopologicalSpace A latticeA
    exact (@orderIsoScottHomeomorph A E latticeA instE e).isInducing.eq_induced
  have heqHome :
      τA = TopologicalSpace.induced (h : A → E) (@scottTopologicalSpace E instE) :=
    (@Homeomorph.isInducing A E τA (@scottTopologicalSpace E instE) h).eq_induced
  exact heqOrder.trans heqHome.symm
end Scott1972.ContinuousLattice
