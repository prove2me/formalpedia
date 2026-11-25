-- Prove2me | solution 1 for PIW.AdelClassFin.stTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:33.926458+00:00
-- url     : https://prove2.me/submissions/d1a53476-1726-48a5-96af-a54054a83b2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : StTop := by
  intro hC hK hG I U hU
  classical
  obtain ⟨g, hg, hgU⟩ := hC I U hU
  obtain ⟨T, hT⟩ := hK I g hg
  obtain ⟨S, hS⟩ := hG I
  refine ⟨(S ×ˢ T).image (fun p => p.1 * p.2), fun x => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := hS x
  obtain ⟨t, ht, u, hu, rfl⟩ := hT k hk
  refine ⟨γ, hγ, s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, u, hgU hu, ?_⟩
  simp only [mul_assoc]
end PIW.AdelClassFin
