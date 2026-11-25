-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:42.97388+00:00
-- url     : https://prove2.me/submissions/4e6209da-16c0-4665-93a0-2e62d86f00bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.GradedPres
namespace GroundTheory.Heights₂.Heights.Kleiman.GradedPres
theorem _root_.solution {S : Type u} [CommRing S] {N : ℕ} {M : Type w}
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (hfin : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (m : Fin r → M) (d : Fin r → ℤ), (∀ j, m j ∈ 𝓜.piece (d j)) ∧
      Submodule.span (Poly S N) (Set.range m) = ⊤ := by
  classical
  let H : Set M := ⋃ c, (𝓜.piece c : Set M)
  have hH : Submodule.span (Poly S N) H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ c, 𝓜.piece c := by
      rw [𝓜.isInternal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction _ (motive := fun y => y ∈ Submodule.span (Poly S N) H) hx
      (fun c y hy => Submodule.subset_span (Set.mem_iUnion.mpr ⟨c, hy⟩)) (zero_mem _)
      (fun a b ha hb => add_mem ha hb)
  have hcomp := (Submodule.fg_iff_compact (⊤ : Submodule (Poly S N) M)).mp hfin.fg_top
  have hle : (⊤ : Submodule (Poly S N) M) ≤ ⨆ h : H, Submodule.span (Poly S N) {(h : M)} := by
    rw [← hH, Submodule.span_le]
    intro y hy
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : H) (Submodule.mem_span_singleton_self y)
  obtain ⟨t, ht⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hcomp _ hle
  let e := t.equivFin
  refine ⟨t.card, fun j => ((e.symm j : H) : M),
    fun j => Classical.choose (Set.mem_iUnion.mp (e.symm j : H).2),
    fun j => Classical.choose_spec (Set.mem_iUnion.mp (e.symm j : H).2), ?_⟩
  rw [eq_top_iff]
  refine ht.trans (iSup₂_le fun h hh => ?_)
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span ⟨e ⟨h, hh⟩, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.GradedPres
