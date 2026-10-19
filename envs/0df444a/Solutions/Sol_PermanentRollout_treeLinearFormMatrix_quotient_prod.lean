-- Prove2me | solution 1 for PermanentRollout.treeLinearFormMatrix_quotient_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/244466ec-246f-418a-bd88-bdc17aed4563

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_eq_column
import Theorems.Thm_PermanentRollout_treeLinearFormVectors_quotient_prod

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (t d : ℕ) (ζ : ℂ) (tree : BlockTree ι) :
    Ideal.Quotient.mk (squareZeroIdeal r)
      (columnLinearFormProduct (treeLinearFormMatrix blocks t d ζ tree)) =
        subtreeLinearFormProduct
          (fun i => squareZeroBlockSum r (blocks i)) t d ζ tree := by
  classical
  calc
    Ideal.Quotient.mk (squareZeroIdeal r)
        (columnLinearFormProduct
          (treeLinearFormMatrix blocks t d ζ tree)) =
        ∏ column : Fin (treeLinearFormVectors blocks t d ζ tree).length,
          treeQuotientLinearForm
            ((treeLinearFormVectors blocks t d ζ tree).get column) := by
              simp only [columnLinearFormProduct, map_prod]
              apply Finset.prod_congr rfl
              intro column _
              exact treeQuotientLinearForm_eq_column
                (treeLinearFormMatrix blocks t d ζ tree) column
    _ = ((treeLinearFormVectors blocks t d ζ tree).map
          treeQuotientLinearForm).prod := by
            rw [← List.prod_ofFn]
            congr 1
            exact List.ofFn_getElem_eq_map
              (treeLinearFormVectors blocks t d ζ tree)
              treeQuotientLinearForm
    _ = subtreeLinearFormProduct
          (fun i => squareZeroBlockSum r (blocks i)) t d ζ tree :=
            treeLinearFormVectors_quotient_prod blocks t d ζ tree
end PermanentRollout
