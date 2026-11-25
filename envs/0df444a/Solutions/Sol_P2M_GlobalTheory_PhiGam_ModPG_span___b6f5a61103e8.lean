-- Prove2me | solution 1 for P2M_GlobalTheory_PhiGam_ModPG_span___b6f5a61103e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:18.663992+00:00
-- url     : https://prove2.me/submissions/83cd4656-36a1-4391-96f6-483f94955f26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k V] {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.PhiGam
namespace ModPG
theorem _root_.solution (D : ModPG R n V) (i : ZMod n) {ι : Type} (b : Module.Basis ι k⸨X⸩ V) :
    Submodule.span k⸨X⸩ (Set.range fun j => D.φ i (b j)) = ⊤ := by
  rw [eq_top_iff, ← D.etale i]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span k⸨X⸩ (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [D.φ_semi i a y]; exact Submodule.smul_mem _ _ hy
end ModPG
end GlobalTheory.PhiGam
