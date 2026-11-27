-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_proof_7d6ddd9200e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:52.645801+00:00
-- url     : https://prove2.me/submissions/d44a758e-35bc-431d-b87b-6699faf33961

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInside
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInside
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622

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
open GroundTheory.Heights₂.Heights.Model.InvOpenInside
namespace GroundTheory.Heights₂.Heights.Model.InvOpenInside
theorem _root_.solution : InvOpenInside.Statement := by
  intro X f _ p W hW
  choose s hsS hs using fun U : X.affineOpens => exists_of_isAffineOpen f p W hW U.2
  have hZ : IsCompact (W : Set X)ᶜ := by
    have hX : IsCompact (Set.univ : Set X) := by
      simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ
    exact hX.of_isClosed_subset W.isOpen.isClosed_compl (Set.subset_univ _)
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun U : X.affineOpens => ((U : X.Opens) : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  set s₀ : ℤ := ∏ U ∈ t, s U with hs₀def
  have hs₀ : s₀ ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl :=
    Submonoid.prod_mem _ fun U _ => hsS U
  have hne : s₀ ≠ 0 := fun h => hs₀ (h ▸ Ideal.zero_mem _)
  refine ⟨s₀.natAbs, Int.natAbs_pos.mpr hne, fun h => ?_, fun x hx => ?_⟩
  · exact hs₀ (Ideal.mem_span_singleton.mpr (Int.ofNat_dvd_left.mpr h))
  · by_contra hxW
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht hxW)
    have h1 := hs U x hxU hxW
    have h2 : s₀ ∈ (f.base x).asIdeal := Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hUt) h1
    exact (mem_invOpen f _ x).mp hx (Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) h2)
end GroundTheory.Heights₂.Heights.Model.InvOpenInside
