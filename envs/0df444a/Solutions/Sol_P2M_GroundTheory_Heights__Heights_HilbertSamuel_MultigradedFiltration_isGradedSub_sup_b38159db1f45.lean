-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isGradedSub_sup_b38159db1f45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:39.358117+00:00
-- url     : https://prove2.me/submissions/b08574fb-958f-4f75-a1f2-e9b4503185ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) :
    IsGradedSub piece (N ⊔ Submodule.span (MRing ι F) {x}) := by
  intro y hy m
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  refine add_mem (Submodule.mem_sup_left (hN a ha m)) (Submodule.mem_sup_right ?_)
  rw [decompose_smul hM s hx m]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
