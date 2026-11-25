-- Prove2me | solution 1 for ReciprocityTheory.PGsh.a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:24:54.828094+00:00
-- url     : https://prove2.me/submissions/def862b5-2375-4cd6-afc4-db3db4e8cce2

import Definitions.Def_ReciprocityTheory_DualLattices_DvdOfCoeffZero
import Definitions.Def_ReciprocityTheory_DualLattices_ValUntiltESubOne
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_ZmodTrichotomy
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_flatW__52449b1b4fd3
import Theorems.Thm_ReciprocityTheory_PGsh_exists_eps
import Theorems.Thm_ReciprocityTheory_PGsh_exists_pflat
import Theorems.Thm_ReciprocityTheory_PGsh_kerTheta
import Theorems.Thm_ReciprocityTheory_PGsh_regular
import Theorems.Thm_ReciprocityTheory_PGsh_xiNu


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
namespace ReciprocityTheory.PGsh
theorem _root_.solution (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by
  intro C _ _ _ v O _ _ hv _ _
  have hK : KerThetaStatement p O := kerTheta (p := p) (C := C) (v := v) (O := O) hv
  have hO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    have h1 := congrArg (algebraMap O C) hx
    rw [map_mul, map_natCast, map_zero] at h1
    apply hv.hom_inj
    rw [map_zero]
    exact (mul_eq_zero.mp h1).resolve_left hp0
  obtain ⟨pf, hpf⟩ := exists_pflat (p := p) (hv := hv)
  exact ⟨⟨pf, hpf⟩, exists_eps (p := p) (hv := hv), hK,
    xiNu p C v O hK, regular (p := p) (O := O) (hO := hO), flatW' (p := p) (O := O)⟩
end ReciprocityTheory.PGsh
