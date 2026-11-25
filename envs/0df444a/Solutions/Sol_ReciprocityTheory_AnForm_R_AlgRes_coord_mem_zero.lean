-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.coord_mem_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:53.424628+00:00
-- url     : https://prove2.me/submissions/0900d07c-7eed-4058-9397-01e20aaea1fb

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) {x : R.M} (hx : x ∈ R.src i) :
    ∀ g ∈ R.ideal i, eval (R.coord i x) g = 0 := by
  have h : R.coord i x ∈ R.coord i '' R.src i := ⟨x, hx, rfl⟩
  rw [R.image i] at h
  exact h
end AlgRes
end ReciprocityTheory.AnForm.R
