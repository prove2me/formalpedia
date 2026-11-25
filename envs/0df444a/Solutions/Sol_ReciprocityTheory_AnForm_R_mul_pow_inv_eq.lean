-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mul_pow_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:51.474399+00:00
-- url     : https://prove2.me/submissions/bd2d1294-0c0a-4aed-9dc1-0e19d8118e09

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R : Type*} [CommRing R] (Q W W' t : R) (c : ℕ) (E : Q * W = W' * W ^ c)
    (ht : W * t = 1) : Q * t ^ c = W' * t := by
  calc Q * t ^ c = Q * t ^ c * (W * t) := by rw [ht, mul_one]
    _ = (Q * W) * t ^ c * t := by ring
    _ = W' * (W * t) ^ c * t := by rw [E]; ring
    _ = W' * t := by rw [ht, one_pow, mul_one]
end ReciprocityTheory.AnForm.R
