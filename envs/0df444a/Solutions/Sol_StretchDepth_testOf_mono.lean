-- Prove2me | solution 1 for StretchDepth.testOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:22:29.286551+00:00
-- url     : https://prove2.me/submissions/5c9c1dfe-cab6-4bea-aefa-e5f7045daf8f

import Definitions.Def_StretchDepth_testOf

namespace StretchDepth


theorem _root_.solution {n N m M : ℕ} (H : Bits m → RoundTree n N M) (τ σ : PartialAssign n N)
    (hτσ : ExtendsPartial τ σ) (y : Bits M) (hy : testOf H τ y = true) :
    testOf H σ y = true := by
  classical
  simp only [testOf, decide_eq_true_eq] at hy ⊢
  obtain ⟨F, hF, hx⟩ := hy
  exact ⟨F, fun w z hz => hF w z (hτσ w z hz), hx⟩
