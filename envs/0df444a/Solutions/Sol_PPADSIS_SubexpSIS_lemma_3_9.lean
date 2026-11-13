-- Prove2me | solution 1 for PPADSIS.SubexpSIS.lemma_3_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @arka
-- created : 2026-11-13T05:42:45.612806+00:00
-- url     : https://prove2.me/submissions/0078cfb6-e7a3-4a2a-a7ce-8933a76811ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PPADSIS_SubexpSIS_searchRTC_spec
import Theorems.Thm_PPADSIS_SubexpSIS_searchRTC_polyTime

open PPADSIS.SubexpSIS

theorem solution :
    ∃ Φ : Circuit → RTC, PPSLattice.PolyTimeOn Circuit.enc (fun φ => (Φ φ).enc) ∧
      ∃ k : ℕ, ∀ φ : Circuit, φ.WF → φ.outs.length = 1 →
        (Φ φ).WF ∧ (Φ φ).p = φ.nIn ∧ (Φ φ).size ≤ (φ.size + 2) ^ k ∧
        (Φ φ).output = searchOutput φ.nIn (fun a => φ.eval a = [true]) :=
  ⟨searchRTC, searchRTC_polyTime, searchRTC_spec⟩
