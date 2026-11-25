-- Prove2me | solution 1 for PI.IsoDerivBFintype.exists_oe_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:28.085609+00:00
-- url     : https://prove2.me/submissions/87d5e88a-9322-4dd7-ae50-eafc12104b97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsoDerivBFintype
namespace PI.IsoDerivBFintype
theorem _root_.solution {h n : ℕ} (f : Fin h → Fin n) (hf : Function.Injective f) :
    ∃ (I : Fin h ↪o Fin n) (σ : Equiv.Perm (Fin h)), ∀ i, I (σ i) = f i := by
  classical
  set s : Finset (Fin n) := Finset.univ.image f with hs
  have hcard : s.card = h := by
    rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
  let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
  have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [g]
  have ginj : Function.Injective g := by
    intro i j e
    apply hf
    rw [← hg i, ← hg j, e]
  exact ⟨s.orderEmbOfFin hcard, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), hg⟩
end PI.IsoDerivBFintype
