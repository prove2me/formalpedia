-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_61a7961cd0e5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:12.309182+00:00
-- url     : https://prove2.me/submissions/afce0dd7-99aa-4bd3-ad8e-7acbaf35e4ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mem_Cdeg_iff_b592b944fd19

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
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A B C : Cell U → Type v}
  [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
  {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J}
  {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
  {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
  {dA : ∀ I, Submodule R (A I)} {dB : ∀ I, Submodule R (B I)} {dC : ∀ I, Submodule R (C I)}
  {φ : ∀ I, A I →ₗ[R] B I} {ψ : ∀ I, B I →ₗ[R] C I}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x) {i : ℕ}
    {s : Cochain B i} (hs : s ∈ Cdeg B dB i) (h0 : mapC ψ i s = 0) :
    ∃ t ∈ Cdeg A dA i, mapC φ i t = s := by
  choose t ht hts using fun I : Idx U i => hmid I.1 (s I) (mem_Cdeg_iff.1 hs I) (congrFun h0 I)
  exact ⟨t, mem_Cdeg_iff.2 ht, funext hts⟩
end GroundTheory.Heights₂.Heights.Kleiman.Cech
