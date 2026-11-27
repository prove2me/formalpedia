-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_InvOpenInsideRat_proof_2bee6c53410f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:47.777958+00:00
-- url     : https://prove2.me/submissions/1f644d3c-2137-4b82-adac-4a9e6978dd6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInsideRat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_range_baseChangeMap_rat_of_asIdeal_eq_bot_27d71feac785

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace InvOpenInsideRat
theorem _root_.solution : InvOpenInsideRat.Statement := by
  intro X f _ _ W hW
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isLocallyNoetherian_of_locallyOfFiniteType_specZ f
  have : IsNoetherian X := {}

  have hgen : ∀ x : X, x ∉ W → (f.base x).asIdeal ≠ ⊥ := by
    intro x hx h
    have h1 := hW (mem_range_baseChangeMap_rat_of_asIdeal_eq_bot f x h)
    rw [Scheme.Opens.range_ι] at h1
    exact hx h1
  obtain ⟨S, hSi, hS⟩ := NoetherianSpace.exists_finset_irreducible
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)
  have hSZ : ∀ k ∈ S, (k : Set X) ⊆ (W : Set X)ᶜ := by
    intro k hk
    have h1 : k ≤ S.sup id := Finset.le_sup (f := id) hk
    rw [← hS] at h1
    exact h1
  have claim : ∀ k ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ (k : Set X), (n : ℤ) ∈ (f.base x).asIdeal := by
    intro k hk
    have hirr : IsIrreducible (k : Set X) := hSi ⟨k, hk⟩
    have hg : IsGenericPoint hirr.genericPoint (k : Set X) :=
      hirr.isGenericPoint_genericPoint k.isClosed
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hgen _ (hSZ k hk hg.mem))
    refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun x hx => ?_⟩
    have hle : (f.base hirr.genericPoint).asIdeal ≤ (f.base x).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hx).map f.base.hom.continuous)
    exact Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) (hle hn)
  choose! n hn using claim
  refine ⟨∏ k ∈ S, n k, Finset.prod_pos fun k hk => (hn k hk).1, ?_⟩
  intro x hx
  by_contra hxW
  have hxS : x ∈ ((S.sup id : Closeds X) : Set X) := by rw [← hS]; exact hxW
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hxS
  obtain ⟨k, hk, hxk⟩ := hxS
  apply (mem_invOpen f _ x).mp hx
  have hdvd : ((n k : ℕ) : ℤ) ∣ ((∏ k ∈ S, n k : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem n hk)
  exact Ideal.mem_of_dvd _ hdvd ((hn k hk).2 x hxk)
end InvOpenInsideRat
end GroundTheory.Heights₂.Heights.Model
