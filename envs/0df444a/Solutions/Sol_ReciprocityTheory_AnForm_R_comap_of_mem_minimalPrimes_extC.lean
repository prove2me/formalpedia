-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:32.855656+00:00
-- url     : https://prove2.me/submissions/008e41a6-db81-4407-9d23-88ad7f23b261

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_flat_mvPolynomial_rat_complex


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
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over
end ReciprocityTheory.AnForm.R
