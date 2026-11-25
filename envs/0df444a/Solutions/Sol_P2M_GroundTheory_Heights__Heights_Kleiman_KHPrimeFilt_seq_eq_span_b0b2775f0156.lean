-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_seq_eq_span_b0b2775f0156
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:31.390135+00:00
-- url     : https://prove2.me/submissions/7a5cc621-2ac4-4345-a36c-d4c2428df948

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt

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
theorem _root_.solution [IsNoetherianRing S] (n : ℕ) :
    seq ι 𝓜 n = Submodule.span (MRingOver S ι) (gen ι 𝓜 '' {l | l < n}) := by
  induction n with
  | zero => simp [seq]
  | succ n ih =>
    have hs : {l : ℕ | l < n + 1} = insert n {l | l < n} := by
      ext l
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
      omega
    show seq ι 𝓜 n ⊔ Submodule.span _ {gen ι 𝓜 n} = _
    rw [hs, Set.image_insert_eq, Submodule.span_insert, sup_comm, ← ih]
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
