-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Gs_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:54.465599+00:00
-- url     : https://prove2.me/submissions/6a9c0d40-176e-46ee-aa88-7b31cd88c7ba

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    Gs χ s x = χ (rsgn x : ZMod l) * ((uphi x * mixedEmbedding.norm x ^ (-s) : ℝ) : ℂ) := by
  unfold Gs
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (mixedEmbedding.norm_nonneg x), Complex.ofReal_neg]
  ring
end ReciprocityTheory.Cheb
