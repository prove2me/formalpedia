-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.claim_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:11.388708+00:00
-- url     : https://prove2.me/submissions/104545cd-f8fb-45e6-95e3-1b1193a33ea1

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_aug
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal) {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N]
    (htriv : ∀ x : N, x = 0) (AA : HopfOrder (C := C) R N) : ClaimBody C v R N AA := by
  haveI : Unique N := ⟨⟨0⟩, htriv⟩
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, fun i => i.elim0, ?_⟩
  · intro f hf
    refine ⟨Fin.elim0, ?_⟩
    have hf0 : f = 0 := by
      funext x
      rw [htriv x]
      exact ((mem_aug _ f).1 hf).2
    simp [hf0]
  · rintro c ⟨B, hB, rfl⟩
    have hrange : (Set.range fun j x => B x j) = {fun x => B x 0} := by
      rw [Set.range_unique]
      congr 1
      funext x
      rw [htriv (default : N)]
    rw [hrange] at hB
    have h1 : (1 : N → C) ∈ Submodule.span R {fun x => B x 0} := by
      rw [← hB]; exact AA.one_mem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
    have hcolmem : (fun x => B x 0) ∈ AA.carrier := by
      rw [hB]; exact Submodule.subset_span rfl
    obtain ⟨s, hs⟩ := AA.le_int hcolmem 0
    have hs' : B 0 0 = algebraMap R C s := hs.symm
    have hdet : B.det = algebraMap R C s := by rw [Matrix.det_unique, htriv (default : N)]; exact hs'
    have hprod : algebraMap R C r * algebraMap R C s = 1 := by
      have h2 := congrFun hr 0
      simp only [Pi.smul_apply, Algebra.smul_def, Pi.one_apply] at h2
      rw [← hs']; exact h2
    have hvs := hv.map_le_one s
    have hv1 : v (algebraMap R C r) * v (algebraMap R C s) = 1 := by
      rw [← map_mul, hprod, map_one]
    have hs1 : v (algebraMap R C s) = 1 := by
      apply le_antisymm hvs
      calc (1 : NNReal) = v (algebraMap R C r) * v (algebraMap R C s) := hv1.symm
        _ ≤ 1 * v (algebraMap R C s) := by gcongr; exact hv.map_le_one r
        _ = _ := one_mul _
    rw [hdet, hs1]
    simp
end ReciprocityTheory.PGsh.Up
