-- Prove2me | solution 1 for PI.LocCartanPair.lag_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:52.393593+00:00
-- url     : https://prove2.me/submissions/d0ee2309-455f-4fba-9a7f-656b95cdb8b5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
import Theorems.Thm_PI_LocCartanPair_lag_reindex
import Theorems.Thm_PI_LocCartanPair_lag_exists_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
namespace PI.LocCartanPair
theorem _root_.solution (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Even (Fintype.card ι)) (A : Matrix ι ι R)
    (hA : Aᴴ = A) (hdet : IsUnit A.det) :
    ∃ e : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) := by
  obtain ⟨m, hm⟩ := hι
  let s : Fin m ⊕ Fin m ≃ ι := Fintype.equivOfCardEq (by simp [hm])
  have hB : (A.submatrix s s)ᴴ = A.submatrix s s := by rw [conjTranspose_submatrix, hA]
  have hBdet : IsUnit (A.submatrix s s).det := by rw [det_submatrix_equiv_self]; exact hdet
  obtain ⟨E, hE, hEA⟩ := lag_exists_sum hR₀ hθ (Fin m) _ hB hBdet
  exact ⟨_, lag_reindex s A E hE hEA⟩
end PI.LocCartanPair
