-- Prove2me | solution 1 for ReciprocityTheory.CA.DepthGE.of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:19.393563+00:00
-- url     : https://prove2.me/submissions/628ac802-4762-416a-a685-d243774212f3

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace DepthGE
theorem _root_.solution {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S) {n : ℕ}
    (h : DepthGE R n) : DepthGE S n := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.map (e : R →+* S), by simp [hlen], ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hy' := hmem y hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
    intro hu
    apply hy'
    simpa using hu.map (e.symm : S →+* R)
  · haveI h1 : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := ⟨by ext; simp, by ext; simp⟩
    have h2 : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := ⟨by ext; simp, by ext; simp⟩
    exact (LinearEquiv.isRegular_congr' (σ' := (e.symm : S →+* R)) e.toSemilinearEquiv rs).mp hreg
end DepthGE
end ReciprocityTheory.CA
