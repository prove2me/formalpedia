-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__teichIota_inj_2f136bef1054
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:58.349802+00:00
-- url     : https://prove2.me/submissions/401f5c68-1420-48a5-b946-07cde156663a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__mem_primeToSub_e38917aa181c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Cardinal
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (x y : AlgebraicClosure (ZMod g)) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxl : (orderOf x).Coprime l) (hyl : (orderOf y).Coprime l)
    (h : teichIota g l x = teichIota g l y) : x = y := by
  have hX : Units.mk0 x hx ∈ primeToSub g l := by
    rw [mem_primeToSub, ← orderOf_units]; exact hxl
  have hY : Units.mk0 y hy ∈ primeToSub g l := by
    rw [mem_primeToSub, ← orderOf_units]; exact hyl
  unfold teichIota at h
  rw [extZeroHom_of_ne _ hx, extZeroHom_of_ne _ hy] at h
  have h1 := Units.ext h
  rw [(iotaU_exists g l).choose_spec ⟨_, hX⟩, (iotaU_exists g l).choose_spec ⟨_, hY⟩] at h1
  have h2 := iotaSub_injective g l h1
  exact congrArg (fun u : primeToSub g l => ((u.1 : (AlgebraicClosure (ZMod g))ˣ) : AlgebraicClosure (ZMod g))) h2
end Formalism.BasicNotions.Examples₂
