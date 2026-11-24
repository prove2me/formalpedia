-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:09.593019+00:00
-- url     : https://prove2.me/submissions/6d64d32a-414f-41d8-9e75-3922bb58e55a

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
theorem _root_.solution (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J) {i : ℕ} {s : Cochain B i}
    (hs : s ∈ Cdeg B dB i) : d B ρB i s ∈ Cdeg B dB (i + 1) := by
  refine mem_Cdeg_iff.2 fun J => ?_
  rw [d_apply]
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (hρB _ _ _ _ (mem_Cdeg_iff.1 hs _)) _
end GroundTheory.Heights₂.Heights.Kleiman.Cech
