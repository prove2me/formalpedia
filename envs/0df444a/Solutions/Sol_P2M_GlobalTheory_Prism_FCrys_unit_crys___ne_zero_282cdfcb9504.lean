-- Prove2me | solution 1 for P2M_GlobalTheory_Prism_FCrys_unit_crys___ne_zero_282cdfcb9504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:51:14.145932+00:00
-- url     : https://prove2.me/submissions/cde4a13f-4da1-4316-a979-f6c895597e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod
namespace GlobalTheory.Prism
namespace FCrys
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] :
    (FCrys.unit l ℤ_[l]).Φ (Obj.crys l) ⟨(l : ℤ_[l]), Ideal.mem_span_singleton_self _⟩ (1 : ℤ_[l]) ≠ 0 := by
  intro h
  have h' : LocalizedModule.mk (1 : ℤ_[l]) (1 : Submonoid.powers (l : ℤ_[l])) =
      LocalizedModule.mk (0 : ℤ_[l]) 1 := by
    rw [LocalizedModule.zero_mk]; exact h
  rw [LocalizedModule.mk_eq] at h'
  obtain ⟨⟨_, r, rfl⟩, h'⟩ := h'
  simp [Submonoid.smul_def, hl.out.ne_zero] at h'
end FCrys
end GlobalTheory.Prism
