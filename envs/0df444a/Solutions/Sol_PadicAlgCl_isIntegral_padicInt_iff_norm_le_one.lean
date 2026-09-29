-- Prove2me | solution 1 for PadicAlgCl.isIntegral_padicInt_iff_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ac367c36-a5c1-59ae-a9b0-8f5b0d45b773

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one

set_option autoImplicit false

noncomputable section

namespace TP9P1

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

theorem norm_le_one_of_isIntegral {x : Ω} (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  have h1 : minpoly ℚ_[p] x = (minpoly ℤ_[p] x).map (algebraMap ℤ_[p] ℚ_[p]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hx
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
  intro n
  rw [h1, coeff_map]
  exact PadicInt.norm_le_one _

theorem isIntegral_of_norm_le_one {x : Ω} (hx : ‖x‖ ≤ 1) : IsIntegral ℤ_[p] x := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hmonic : (minpoly ℚ_[p] x).Monic := minpoly.monic hint
  have hcoeff : ∀ n, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmonic]
    change spectralNorm ℚ_[p] Ω x ≤ 1
    rwa [PadicAlgCl.spectralNorm_eq]

  have hlifts : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨(minpoly ℚ_[p] x).coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonic
  refine ⟨g, hgmonic, ?_⟩
  rw [← aeval_def, ← minpoly.aeval ℚ_[p] x, aeval_def, aeval_def,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] Ω, ← eval₂_map, hgmap]

theorem main (x : Ω) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  ⟨norm_le_one_of_isIntegral p, isIntegral_of_norm_le_one p⟩

end TP9P1

end

theorem solution (p : ℕ) [Fact p.Prime] (x : PadicAlgCl p) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 :=
  TP9P1.main p x

end S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
end P2MW
export P2MW.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one (solution)
