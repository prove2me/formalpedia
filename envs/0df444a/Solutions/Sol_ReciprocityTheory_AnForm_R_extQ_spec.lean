-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.extQ_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:51.183331+00:00
-- url     : https://prove2.me/submissions/6c5852af-43e2-4844-b0b8-83a8dd0c1a48

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_coheight_eQ_add_one_le
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_map_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_length_le_coheight_eQ
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_map_isPrime
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_ringKrullDim_quotient_eq_coheight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IntegerToRational
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0) :
    (extQ P).IsPrime ∧ (extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P ∧
      ringKrullDim (MvPolynomial σ ℚ ⧸ extQ P) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hP' : ChZero P := hP
  haveI hI : (extQ P).IsPrime := map_isPrime P hP'
  refine ⟨hI, comap_map_eq P hP', ?_⟩
  have h1 := coheight_eQ_add_one_le (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) hP'
  have h2 : Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) ≤
      Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 :=
    Order.coheight_le fun s hs => length_le_coheight_eQ s _ hs hP'
  have heq : Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 =
      Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) :=
    le_antisymm h1 h2
  have hE : (⟨extQ P, hI⟩ : PrimeSpectrum (MvPolynomial σ ℚ)) = eQ ⟨P, inferInstance⟩ hP' := rfl
  rw [ringKrullDim_quotient_eq_coheight (extQ P), ringKrullDim_quotient_eq_coheight P, hE, ← heq]
  norm_cast
end ReciprocityTheory.AnForm.R
