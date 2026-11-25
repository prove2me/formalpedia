-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.cmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:55.223933+00:00
-- url     : https://prove2.me/submissions/084c504a-884a-4c5f-81c7-08ea5eef2646

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
variable (hv : v.Integers R)
include hv
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution {X : Type} (M : Submodule R (X → C)) {c : C} (hc : v c ≤ 1) {f : X → C}
    (hf : f ∈ M) : (fun t => c * f t) ∈ M := by
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hc
  have e : (fun t => c * f t) = r • f := by
    funext t
    simp [Algebra.smul_def, hr]
  rw [e]
  exact M.smul_mem r hf
end ReciprocityTheory.PGsh.Up.U3
