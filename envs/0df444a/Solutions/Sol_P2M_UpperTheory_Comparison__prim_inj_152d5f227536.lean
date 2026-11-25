-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__prim_inj_152d5f227536
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:56.354556+00:00
-- url     : https://prove2.me/submissions/e5073be4-ce93-453c-9e42-ebf377924679

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimInj
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_dir_unit
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by
  intro φ H
  constructor
  · intro θ θ' h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
    have h1 := (H.toHostRaw.isPrimOf_prim θ).2
    have h2 := (H.toHostRaw.isPrimOf_prim θ').2
    rw [← h] at h2
    have hc := ZMod.val_coe_unit_coprime u
    have e := (h1 _ hc).symm.trans (h2 _ hc)
    apply Units.ext
    rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
    simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
  · have hd : H.toHostRaw.dir 1 = 1 := by
      apply MulChar.ext
      intro u
      rw [HostRaw.dir_unit]
      simp
    rw [HostRaw.prim, hd, PChar.of_one]
end UpperTheory.Comparison₂
