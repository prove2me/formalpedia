-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.eQ_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:02.457669+00:00
-- url     : https://prove2.me/submissions/797a4baa-5920-4625-bd55-bee458bc9184

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_map_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by
  have hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal := by
    show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal
    exact Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)
  show (eQ x hx).asIdeal < (eQ y hy).asIdeal
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) =
      (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) := congrArg (Ideal.comap _) heq
  rw [comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy] at h2
  exact (show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2
end ReciprocityTheory.AnForm.R.IntegerToRational
