-- Prove2me | solution 1 for Reformulated.AutPerF.exists_sum_wittResidueToRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:20.704367+00:00
-- url     : https://prove2.me/submissions/7d212263-fc62-4f04-bf20-3ea8c1d92974

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
import Theorems.Thm_Reformulated_AutPerF_residue_wittResidueToRing
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
open Reformulated Reformulated.AutPerF
universe u
variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]
variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]
variable [IsAdicComplete (span {(p : A)}) A]
namespace Reformulated.AutPerF
theorem _root_.solution {π : A} (hπ : Irreducible π) (n : ℕ) (a : A) :
    ∃ (c : ℕ → WittVector p (ResidueField A)) (b : A),
      a = ∑ i ∈ Finset.range n, wittResidueToRing p A (c i) * π ^ i + π ^ n * b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨c, b, rfl⟩ := ih
    have : b - wittResidueToRing p A (WittVector.teichmuller p (residue A b)) ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, residue_wittResidueToRing,
        WittVector.teichmuller_coeff_zero, sub_self]
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨d, hd⟩ := this
    refine ⟨Function.update c n (WittVector.teichmuller p (residue A b)), d, ?_⟩
    have hs : ∑ i ∈ Finset.range n, wittResidueToRing p A
        (Function.update c n (WittVector.teichmuller p (residue A b)) i) * π ^ i =
        ∑ i ∈ Finset.range n, wittResidueToRing p A (c i) * π ^ i :=
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
    rw [Finset.sum_range_succ, Function.update_self, hs]
    rw [sub_eq_iff_eq_add] at hd
    conv_lhs => rw [hd]
    ring
end Reformulated.AutPerF
