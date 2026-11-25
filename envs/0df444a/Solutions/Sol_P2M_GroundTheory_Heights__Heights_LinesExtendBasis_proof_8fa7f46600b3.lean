-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesExtendBasis_proof_8fa7f46600b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:47.743422+00:00
-- url     : https://prove2.me/submissions/bc777f61-f11f-40c4-aa4b-e3d511a7d70e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesExtendBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open KLinesExtendBasis
namespace GroundTheory.Heights₂.Heights
namespace LinesExtendBasis
theorem _root_.solution : LinesExtendBasis.Statement := by
  intro K _ n m k b hb hn
  set W : Submodule K (Fin n → K) := Submodule.span K (Set.range b) with hW
  let e : Fin n → (Fin n → K) := fun x => Pi.single x 1
  have hspan : Submodule.span K (Set.range (W.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, span_single_eq_top, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ : ∃ (κ : Type) (a : κ → Fin n), Function.Injective a ∧
      Submodule.span K (Set.range ((W.mkQ ∘ e) ∘ a)) = Submodule.span K (Set.range (W.mkQ ∘ e)) ∧
      LinearIndependent K ((W.mkQ ∘ e) ∘ a) := exists_linearIndependent' K (W.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ K ((Fin n → K) ⧸ W) := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = k := by
    have h1 := W.finrank_quotient_add_finrank
    rw [Module.finrank_eq_card_basis B, hW, finrank_span_eq_card hb, Module.finrank_fin_fun,
      Fintype.card_fin] at h1
    omega
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ σ, ha.comp σ.injective, ?_⟩
  let f : Fin m → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp W.subtype hb
  have hg : LinearIndependent K (Submodule.Quotient.mk (p := W) ∘ fun j => e (a (σ j))) :=
    hli.comp σ σ.injective
  exact LinearIndependent.sumElim_of_quotient hf (fun j => e (a (σ j))) hg
end LinesExtendBasis
end GroundTheory.Heights₂.Heights
