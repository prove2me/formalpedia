-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:54.545299+00:00
-- url     : https://prove2.me/submissions/6938626d-7250-4522-b28c-c39528b0768a

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_isLat_map_equiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_hopfLat
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution (v : Valuation C NNReal) (hv : v.Integers R) {N X : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] [AddCommGroup X] [Fintype X] [DecidableEq X]
    (ψ : X →+ N) (hψ : Function.Injective ψ) (AA : HopfOrder (C := C) R N) :
    IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ)) := by
  classical
  obtain ⟨⟨AK, hAK⟩, -⟩ := h2 C R v hv N ψ.range AA
  let e := AddMonoidHom.ofInjective hψ
  have hmap : (AA.carrier.map (resK ψ.range)).map (LinearMap.funLeft R C e.toEquiv) =
      AA.carrier.map (LinearMap.funLeft R C ψ) := by
    rw [← Submodule.map_comp]
    congr 1
  rw [← hmap, ← hAK]
  exact isLat_map_equiv e.toEquiv (hopfLat AK)
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
