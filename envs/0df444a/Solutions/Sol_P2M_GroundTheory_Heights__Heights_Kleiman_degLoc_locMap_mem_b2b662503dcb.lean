-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_degLoc_locMap_mem_b2b662503dcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:42.424889+00:00
-- url     : https://prove2.me/submissions/8a631b97-8edb-48ea-826a-84e5cd4205f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact

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
universe u v
universe w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (c : ℤ) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    locMap f.toLin I.1 x ∈ degLoc 𝓜' c I := by
  refine Submodule.span_induction (p := fun x _ => (locMap f.toLin I.1).restrictScalars S x ∈
    degLoc 𝓜' c I) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    exact Submodule.subset_span ⟨f.toLin m, s, a, e, f.map_piece a m hm, hs, hae,
      locMap_mk f.toLin I.1 m s⟩
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx
end GroundTheory.Heights₂.Heights.Kleiman
