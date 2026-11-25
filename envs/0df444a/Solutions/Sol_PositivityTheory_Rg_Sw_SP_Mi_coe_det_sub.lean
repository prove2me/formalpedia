-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.coe_det_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:36.388243+00:00
-- url     : https://prove2.me/submissions/4f7401d6-bd0e-45ea-bf22-2f06c1692a35

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_coe_list_prod
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_gens_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α : R) (ρ r : ℕ) (I J : Fin r → Fin ρ) :
    letI : CommRing (Algebra.adjoin R (gens α ρ)) := Algebra.adjoinCommRingOfComm R (gens_comm α ρ)
    ((((Aop α ρ).submatrix I J).det : Algebra.adjoin R (gens α ρ)) : Module.End R (Pm R ρ)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) •
        ((List.finRange r).map (fun k => opE α (I k) (J (σ k)))).prod := by
  letI : CommRing (Algebra.adjoin R (gens α ρ)) := Algebra.adjoinCommRingOfComm R (gens_comm α ρ)
  rw [← det_transpose, det_apply']
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Subalgebra.coe_mul, ← List.prod_ofFn, coe_list_prod, List.ofFn_eq_map, List.map_map]
  have hε : (((((Equiv.Perm.sign σ : ℤ) : Algebra.adjoin R (gens α ρ))) : Module.End R (Pm R ρ))) =
      ((Equiv.Perm.sign σ : ℤ) : Module.End R (Pm R ρ)) := by push_cast; rfl
  rw [hε, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul R]
  rfl
end PositivityTheory.Rg.Sw.SP.Mi
