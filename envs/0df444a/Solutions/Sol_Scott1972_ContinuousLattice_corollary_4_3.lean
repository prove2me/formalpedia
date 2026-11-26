-- Prove2me | solution 1 for Scott1972.ContinuousLattice.corollary_4_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:40.947636+00:00
-- url     : https://prove2.me/submissions/7a9a2ce1-2434-4861-8b59-eba899234607

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_embInf_family_directed
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_eq_iSup
import Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_comp_embInf
import Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) :
    ∃! g : ScottMap (InverseLimit D P) D', ∀ n x, f n x = g (embInf D P n x) := by
  refine ⟨⟨coconeInf D P f,
    continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)⟩, ?_, ?_⟩
  · exact fun n x => (coconeInf_comp_embInf D P f hf n x).symm
  · intro g hg
    ext x
    -- `g x = f∞ x`, since `x = ⨆ₙ i_{n∞}(xₙ)` and `g` is continuous on this directed family
    calc g x = g (⨆ n, embInf D P n (x.1 n)) := by rw [← inverseLimit_eq_iSup D P x]
      _ = g (sSup (Set.range fun n => embInf D P n (x.1 n))) := by rw [sSup_range]
      _ = sSup (g '' Set.range fun n => embInf D P n (x.1 n)) :=
          g.preservesDirectedSup_coe _ (Set.range_nonempty _) (embInf_family_directed D P x)
      _ = ⨆ n, g (embInf D P n (x.1 n)) := by rw [← Set.range_comp, sSup_range]; rfl
      _ = ⨆ n, f n (x.1 n) := by simp_rw [← hg]
end Scott1972.ContinuousLattice
