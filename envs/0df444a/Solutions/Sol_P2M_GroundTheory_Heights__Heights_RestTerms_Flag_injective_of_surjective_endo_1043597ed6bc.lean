-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:12.284261+00:00
-- url     : https://prove2.me/submissions/50840b51-3e79-429c-84f4-646bd23b5088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩
  have hsurj : ∀ n, Function.Surjective (φ^[n]) := fun n => hφ.iterate n
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr
    (isNoetherianRing_iff.mp inferInstance) K
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ K (n + 1) := by
    show (φ ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  have h' : (φ ^ n) y = 0 := hy
  simpa [RingHom.coe_pow] using h'
end GroundTheory.Heights₂.Heights.RestTerms.Flag
