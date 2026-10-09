-- Prove2me | solution 1 for OCB2012.isProcessMatrix_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:08:54.866808+00:00
-- url     : https://prove2.me/submissions/22254976-2875-4113-a97b-bf47aba1e0cd

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_OCB2012_process_condition_iff_allowed

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (BA1 : HSBasis a1) (BA2 : HSBasis a2) (BB1 : HSBasis b1) (BB2 : HSBasis b2)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) :
    IsProcessMatrix W ↔
      (W.PosSemidef ∧ W.trace = (Fintype.card a2 * Fintype.card b2 : ℂ) ∧
        ∀ μ ν l γ, ¬ AllowedType μ.isSome ν.isSome l.isSome γ.isSome →
          (W * ((BA1.σ μ ⊗ₖ BA2.σ ν) ⊗ₖ (BB1.σ l ⊗ₖ BB2.σ γ))).trace = 0) := by
  constructor
  · rintro ⟨hpsd, hprob⟩
    exact ⟨hpsd,
      (OCB2012.process_condition_iff_allowed BA1 BA2 BB1 BB2 W hpsd.isHermitian).1 hprob⟩
  · rintro ⟨hpsd, hcond⟩
    exact ⟨hpsd,
      (OCB2012.process_condition_iff_allowed BA1 BA2 BB1 BB2 W hpsd.isHermitian).2 hcond⟩
