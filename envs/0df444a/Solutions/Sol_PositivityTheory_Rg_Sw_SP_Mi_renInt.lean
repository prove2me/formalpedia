-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.renInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:57.530074+00:00
-- url     : https://prove2.me/submissions/5868fce1-6f16-4d4a-8d0b-8b41f83103db

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB

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
theorem _root_.solution : RenInt := by
  intro R _ r s I J α p q f
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_add, map_mul]
  congr 1
  · simp [ren, rename_X]
  · induction f using MvPolynomial.induction_on with
    | C a => simp [ren]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f ad hf =>
      have e1 : ren I J (f * X ad) = ren I J f * X (J ad.1, I ad.2) := by simp [ren, rename_X]
      rw [e1, Derivation.leibniz, Derivation.leibniz, map_add, hf, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      simp only [del, mkDerivation_X, ren, map_mul, rename_X]
end PositivityTheory.Rg.Sw.SP.Mi
