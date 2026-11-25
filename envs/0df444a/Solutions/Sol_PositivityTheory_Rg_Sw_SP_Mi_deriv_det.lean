-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.deriv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:56.094442+00:00
-- url     : https://prove2.me/submissions/d75e954d-6ef9-409b-991d-8b32a9fcc03e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_deriv_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A) {ρ : ℕ}
    (M : Matrix (Fin ρ) (Fin ρ) A) :
    D M.det = ∑ c, (Matrix.updateCol M c (fun a => D (M a c))).det := by
  simp only [Matrix.det_apply]
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.map_smul_of_tower, deriv_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  simp only [Matrix.updateCol_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]
end PositivityTheory.Rg.Sw.SP.Mi
