-- Prove2me | solution 1 for OPG401.common_allowed_colors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T15:49:35.005717+00:00
-- url     : https://prove2.me/submissions/1d18d4de-31f7-4b44-952c-0d361760ade1

import Mathlib
import Definitions.Def_opg401_circular_coloring

open Finset

namespace OPG401aux

instance decPQ (p q : ℕ) (a b : Fin p) : Decidable (OPG401.PQCompatible p q a b) :=
  inferInstanceAs (Decidable (q ≤ OPG401.circularDistance a b ∧
    OPG401.circularDistance a b ≤ p - q))

/-- `allowedColors` is defined through a classical decidability instance; this
replaces it by the computable one. -/
lemma allowed_eq (a : Fin 20) :
    OPG401.allowedColors a
      = Finset.univ.filter (fun z => OPG401.PQCompatible 20 7 z a) := by
  unfold OPG401.allowedColors
  exact Finset.filter_congr_decidable _ _ _

end OPG401aux

set_option maxRecDepth 40000 in
theorem solution (a b : Fin 20) :
    ((OPG401.allowedColors a ∩ OPG401.allowedColors b).card
        = 7 - OPG401.circularDistance a b) ∧
    ((OPG401.allowedColors a ∩ OPG401.allowedColors b).Nonempty
        ↔ OPG401.circularDistance a b ≤ 6) := by
  have key : ∀ x y : Fin 20,
      (((Finset.univ.filter (fun z => OPG401.PQCompatible 20 7 z x)) ∩
        (Finset.univ.filter (fun z => OPG401.PQCompatible 20 7 z y))).card
          = 7 - OPG401.circularDistance x y) ∧
      ((((Finset.univ.filter (fun z => OPG401.PQCompatible 20 7 z x)) ∩
        (Finset.univ.filter (fun z => OPG401.PQCompatible 20 7 z y))).Nonempty)
          ↔ OPG401.circularDistance x y ≤ 6) := by decide +kernel
  rw [OPG401aux.allowed_eq a, OPG401aux.allowed_eq b]
  exact key a b
