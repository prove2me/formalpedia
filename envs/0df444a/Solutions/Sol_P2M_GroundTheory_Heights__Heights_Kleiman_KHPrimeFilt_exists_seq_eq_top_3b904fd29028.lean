-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_exists_seq_eq_top_3b904fd29028
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:07.916742+00:00
-- url     : https://prove2.me/submissions/f6a0fee0-fb87-4a70-b958-5ae0ed35f3ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_next_spec_72b93845cbd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_seq_isGradedSub_971d8254db49

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 2000] lexDecEq
variable (ι 𝓜)
variable {ι 𝓜}
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution [IsNoetherianRing S] [Module.Finite (MRingOver S ι) M]
    (hgr : IsMGraded S ι 𝓜) : ∃ n, seq ι 𝓜 n = ⊤ := by
  have hmono : Monotone (seq ι 𝓜) := monotone_nat_of_le_succ fun k => le_sup_left
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MRingOver S ι) M) ⟨seq ι 𝓜, hmono⟩
  refine ⟨n, by_contra fun hne => ?_⟩
  have hp := (next_spec hgr (seq_isGradedSub hgr n) hne).1
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, mem_colon, one_smul]
  have h1 : (next ι 𝓜 (seq ι 𝓜 n)).1 ∈ seq ι 𝓜 (n + 1) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2 : seq ι 𝓜 n = seq ι 𝓜 (n + 1) := hn (n + 1) (Nat.le_succ n)
  rwa [← h2] at h1
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
