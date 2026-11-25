-- Prove2me | solution 1 for ReciprocityTheory.CA.exch_socle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:12.73388+00:00
-- url     : https://prove2.me/submissions/32ee3943-dc83-4f21-80a1-dcd857bd2b4c

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
theorem _root_.solution {x y : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) {a : M} (ha : a ∉ x • (⊤ : Submodule R M))
    (hma : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)) :
    ∃ b : M, b ∉ y • (⊤ : Submodule R M) ∧
      ∀ z ∈ maximalIdeal R, z • b ∈ y • (⊤ : Submodule R M) := by
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma y hy)
  refine ⟨b, ?_, ?_⟩
  · intro hby
    obtain ⟨b', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hby
    apply ha
    have : y • a = y • (x • b') := by rw [← hb, smul_comm]
    rw [ry this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro z hz
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma z hz)
    have : x • (z • b) = x • (y • c) := by
      rw [smul_comm x z, hb, smul_comm x y, hc, smul_comm]
    rw [rx this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
end ReciprocityTheory.CA
