-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.IK_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:04.486716+00:00
-- url     : https://prove2.me/submissions/695a8c1f-6848-4994-8dbe-70eb16dd0a18

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_aug

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable (K : AddSubgroup N) [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) :
    (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  rw [Submodule.mul_le]
  intro m hm a ha
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hm
  rw [mem_aug] at hb
  obtain ⟨r, hr⟩ := AA.le_int ha 0
  have hpb : pullQ (R := R) K b ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    exact ⟨hb.1, by simpa [pullQ, LinearMap.funLeft_apply] using hb.2⟩
  have ha' : a - r • (1 : N → C) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem), ?_⟩
    simp [Algebra.smul_def, hr]
  have hsplit : pullQ (R := R) K b * a =
      pullQ (R := R) K b * (a - r • (1 : N → C)) + r • pullQ (R := R) K b := by
    rw [mul_sub, mul_smul_comm, mul_one]
    abel
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul hpb ha')) ?_
  refine Submodule.mem_sup_left ?_
  exact Submodule.smul_mem _ r (Submodule.mem_map_of_mem (by rw [mem_aug]; exact hb))
end ReciprocityTheory.PGsh.Up
