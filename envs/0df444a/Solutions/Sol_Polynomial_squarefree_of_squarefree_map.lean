-- Prove2me | solution 1 for Polynomial.squarefree_of_squarefree_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4d06dabc-a9f1-5352-8409-569889cc5712

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_squarefree_of_squarefree_map
open Polynomial

theorem solution {κ L : Type*} [Field κ] [CommRing L] [IsDomain L]
    (φ : κ →+* L) {f : κ[X]} (hf : Squarefree (f.map φ)) : Squarefree f := by
  have hφ : Function.Injective φ := φ.injective
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  intro g hg
  have hgmap : IsUnit (g.map φ) := by
    apply hf
    have := _root_.map_dvd (Polynomial.mapRingHom φ) hg
    simpa [Polynomial.map_mul] using this
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
    exact hf0 hg
  rw [Polynomial.isUnit_iff] at hgmap ⊢
  obtain ⟨r, hr, hrg⟩ := hgmap
  have hdeg : g.natDegree = 0 := by
    rw [← natDegree_map_eq_of_injective hφ, ← hrg, natDegree_C]
  refine ⟨g.coeff 0, ?_, (eq_C_of_natDegree_eq_zero hdeg).symm⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hg0
  rw [eq_C_of_natDegree_eq_zero hdeg, h0, map_zero]

end S_Polynomial_squarefree_of_squarefree_map
end P2MW
export P2MW.S_Polynomial_squarefree_of_squarefree_map (solution)
