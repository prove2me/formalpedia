-- Prove2me | solution 1 for TaylorWiles.exists_isEigenIdempotent_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/efd128eb-93aa-5612-b76d-19bbad37adc2

import Mathlib
import Definitions.Def_Deformations_LocalSplitting
import Theorems.Thm_TaylorWiles_isEigenIdempotent_smul_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit

set_option autoImplicit false

universe u v

open Matrix

open TaylorWiles in
theorem solution {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨_, TaylorWiles.isEigenIdempotent_smul_sub htr hdet (v := ((u⁻¹ : Aˣ) : A)) ?_⟩
  rw [← hu]
  exact u.inv_mul

end S_TaylorWiles_exists_isEigenIdempotent_of_isUnit
end P2MW
export P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit (solution)
