-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.finite_cohomology_of_isFG
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9a97055f-f551-5de9-832e-b65bed31a4c2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
import Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG
import Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "GradedModule GradedModule.H GradedModule.subsingleton_cohomology_of_lt GradedModule.Presentation GradedModule.IsFG GradedModule.Presentation.finite_H_of_ses GradedModule.Presentation.ker_isFG GradedModule.finite_cohomology_pi_FD"
p2m_open "ProjSpaceCech"

section Main

variable {R : Type u} [CommRing R] {n : ℕ}

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "H subsingleton_cohomology_of_lt Presentation IsFG Presentation.finite_H_of_ses Presentation.ker_isFG finite_cohomology_pi_FD" end GradedModule
p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.finite_cohomology_of_isFG' [IsNoetherianRing R] (D : GradedModule R n)
    (hD : GradedModule.IsFG D) (i : ℕ) :
    Module.Finite R (GradedModule.H D i) := by

  suffices h : ∀ i, ∀ (D' : GradedModule R n), GradedModule.IsFG D' →
      Module.Finite R (GradedModule.H D' i) from h i D hD
  intro i
  induction i using Nat.strong_decreasing_induction with
  | base =>
    refine ⟨n, fun m hm D' _ => ?_⟩
    haveI := GradedModule.subsingleton_cohomology_of_lt D' hm
    infer_instance
  | step i IH =>
    intro D' ⟨σ⟩
    refine GradedModule.Presentation.finite_H_of_ses σ i ?_ ?_
    · exact GradedModule.finite_cohomology_pi_FD R n σ.d₀ i
    · exact IH (i + 1) (Nat.lt_succ_self i) σ.ker (GradedModule.Presentation.ker_isFG σ)

end Main

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n)
    (hD : ProjSpaceCech.GradedModule.IsFG D) (i : ℕ) : Module.Finite R (ProjSpaceCech.GradedModule.H D i) :=
  ProjSpaceCech.GradedModule.finite_cohomology_of_isFG' D hD i

end

end S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG (solution)
