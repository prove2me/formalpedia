-- Prove2me | solution 1 for PackedProduct.isBounded_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:36:14.046782+00:00
-- url     : https://prove2.me/submissions/69beec65-58a3-4364-94f2-194417402d02

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle


set_option autoImplicit false

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 3744-3750

theorem solution {n m : ℕ} (s : Set (BregmanPPA.ProxMult.PD n m)) :
    Bornology.IsBounded s ↔
      Bornology.IsBounded ((fun z => (WithLp.ofLp z).1) '' s) ∧
      Bornology.IsBounded ((fun z => (WithLp.ofLp z).2) '' s) := by
  change @Bornology.IsBounded _ (Bornology.induced
    (@WithLp.ofLp 2 (BregmanPPA.IneqMult.E n × BregmanPPA.IneqMult.E m))) s ↔ _
  rw [Bornology.isBounded_induced,← Bornology.isBounded_image_fst_and_snd]
  simp only [Set.image_image,Function.comp_def]
