-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:32.769934+00:00
-- url     : https://prove2.me/submissions/62241e2d-77af-4ef6-957c-e9f02fc1c435

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by
  unfold IsMultiHomogeneous at hf ⊢
  first
  | exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)
  | exact fun b => (hf b).map φ
  | simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf
  | (intro d hd
     simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd
     exact hf d (by simpa using hd))
end ReciprocityTheory.MultiplicativeHeights
