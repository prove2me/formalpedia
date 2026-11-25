-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.isOpen_setOf_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:13.468982+00:00
-- url     : https://prove2.me/submissions/7b878e48-b334-4393-83d8-dabb123ae911

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal]
    (hNc : IsClosed (N : Set G)) [CompactSpace G] (f : N → M.V) (hf : Continuous f) (m : M.V) :
    IsOpen {s : G | ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m} := by
  have hact : Continuous (fun q : G × M.V => M.rho q.1 q.2) := M.cont
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp hNc.isCompact
  have hcj : Continuous (fun p : G × N => cj N p.1 p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst
  have hΦ : Continuous (fun p : G × N =>
      M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m)) := by
    refine ((hact.comp (continuous_fst.prodMk (hf.comp hcj))).sub (hf.comp continuous_snd)).sub ?_
    exact (hact.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)).sub
      continuous_const
  have hO : IsOpen {p : G × N | M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m) = 0} :=
    hΦ.isOpen_preimage {0} (isOpen_discrete _)
  rw [isOpen_iff_mem_nhds]
  intro s0 hs0
  have hev : ∀ᶠ s in nhds s0, ∀ n ∈ (Set.univ : Set N),
      M.rho s (f (cj N s n)) - f n - (M.rho (n : G) m - m) = 0 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro n _
    exact hO.mem_nhds (sub_eq_zero.mpr (hs0 n))
  filter_upwards [hev] with s hs n
  exact sub_eq_zero.mp (hs n (Set.mem_univ n))
end ReciprocityTheory.Coh.InflationTransgression
