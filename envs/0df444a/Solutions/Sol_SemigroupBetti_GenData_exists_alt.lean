-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:00:35.790307+00:00
-- url     : https://prove2.me/submissions/0eb7e7ae-31ab-4179-b0f3-68c93ef3915c

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_crit_spec

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) :
    ∃ y : Fin 4 → ℕ, G.nu y = G.crit i * G.n i ∧ y ≠ Pi.single i (G.crit i) :=
  (G.isCritCand_iff.1 (G.crit_spec i)).2
end SemigroupBetti.GenData
