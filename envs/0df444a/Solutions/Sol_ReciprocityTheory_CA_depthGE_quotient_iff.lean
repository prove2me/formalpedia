-- Prove2me | solution 1 for ReciprocityTheory.CA.depthGE_quotient_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:04.620503+00:00
-- url     : https://prove2.me/submissions/1372b8d5-61cd-4b41-b5ee-a4b24ccb53f4

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Theorems.Thm_P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422
import Theorems.Thm_ReciprocityTheory_CA_mk_mem_maximalIdeal_quot

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
theorem _root_.solution (I : Ideal R) [IsLocalRing (R ⧸ I)] (n : ℕ) :
    DepthGE (R ⧸ I) n ↔ ModDepthGE R (R ⧸ I) n := by
  have key : ∀ rs : List R, RingTheory.Sequence.IsRegular (R ⧸ I) (rs.map (Ideal.Quotient.mk I)) ↔
      RingTheory.Sequence.IsRegular (R ⧸ I) rs := fun rs => by
    have := isRegular_map_algebraMap_iff' (S := R ⧸ I) (M := R ⧸ I) rs
    rwa [Ideal.Quotient.algebraMap_eq] at this
  have hs : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  constructor
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Function.surjInv hs), by simp [hlen], ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hy' := hmem y hy
      rw [← Function.surjInv_eq hs y] at hy'
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy' ⊢
      exact fun hu => hy' (hu.map _)
    · have hl : (rs.map (Function.surjInv hs)).map (Ideal.Quotient.mk I) = rs := by
        simp [Function.comp_def, Function.surjInv_eq hs]
      rw [← key, hl]
      exact hreg
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (Ideal.Quotient.mk I), by simp [hlen], ?_, (key rs).mpr hreg⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact mk_mem_maximalIdeal_quot I (hmem y hy)
end ReciprocityTheory.CA
