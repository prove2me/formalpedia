-- Prove2me | solution 1 for ReciprocityTheory.CA.pstep_monic_mem_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:53.773505+00:00
-- url     : https://prove2.me/submissions/c6717827-c545-4268-abe0-e4299eac2c89

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial RingTheory.Sequence
namespace ReciprocityTheory.CA
theorem _root_.solution {S : Type*} [CommRing S] (J : Ideal S) {g h : S[X]} (hg : g.Monic)
    (hgh : g * h ∈ J.map (C : S →+* S[X])) : h ∈ J.map (C : S →+* S[X]) := by

  have hk : RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) = J.map (C : S →+* S[X]) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hk, RingHom.mem_ker] at hgh ⊢
  simp only [map_mul, coe_mapRingHom] at hgh
  rw [coe_mapRingHom]
  exact ((hg.map (Ideal.Quotient.mk J)).mul_right_eq_zero_iff).mp hgh
end ReciprocityTheory.CA
