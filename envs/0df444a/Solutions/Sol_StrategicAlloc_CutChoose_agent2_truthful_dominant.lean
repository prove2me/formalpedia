-- Prove2me | solution 1 for StrategicAlloc.CutChoose.agent2_truthful_dominant
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:18.690183+00:00
-- url     : https://prove2.me/submissions/550383ce-4141-441c-814a-35436b774a4a

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

set_option autoImplicit false
open StrategicAlloc.CutChoose

theorem solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) (hb : StrategicAlloc.RRFair.IsBidProfile b) :
    StrategicAlloc.RRFair.IsBestResponse modCutChoose v (Function.update b 1 (v 1)) 1 := by
  intro b' hb'
  have h0 : ∀ c : Fin m → ℝ, Function.update (Function.update b 1 (v 1)) 1 c 0 = b 0 := by
    intro c
    simp [Function.update_apply]
  have h1 : ∀ c : Fin m → ℝ, Function.update (Function.update b 1 (v 1)) 1 c 1 = c := by
    intro c
    simp
  have h0' : Function.update b 1 (v 1) 0 = b 0 := by simp [Function.update_apply]
  have h1' : Function.update b 1 (v 1) 1 = v 1 := by simp
  simp only [modCutChoose, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, h0, h1, h0', h1']
  unfold StrategicAlloc.RRFair.val
  split_ifs with hc hc' hc' <;> first | exact le_rfl | linarith
