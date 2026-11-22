-- Prove2me | solution 1 for P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:56.629205+00:00
-- url     : https://prove2.me/submissions/9b0abdf8-d26a-48d6-9210-e7f6f6c0ee7c

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (x : n → A) :
    x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, x i ∈ Set.range (algebraMap R A) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
    Algebra.linearMap_apply, Set.mem_range]
end Formalism.UG.P
