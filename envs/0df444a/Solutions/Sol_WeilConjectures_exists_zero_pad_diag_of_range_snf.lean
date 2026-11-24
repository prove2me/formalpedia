-- Prove2me | solution 1 for WeilConjectures.exists_zero_pad_diag_of_range_snf
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:04:49.009683+00:00
-- url     : https://prove2.me/submissions/475c7e7f-5a01-40d8-846c-4690c65475d3

import Mathlib

/-!
A52 CLASSICAL-SNF-CHOICE / A50: zero-pad SNF coeffs via Classical.choose
on Nonempty range-SNF; `dite` on `∃ j, f j = i`. 0-child.
-/

open Classical

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (hSNF : ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      ∀ M, ∃ (n : ℕ)
        (snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n),
        (∀ j, d M (snf.f j) = snf.a j) ∧
          (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) := by
  refine ⟨fun M i =>
      let n := (hSNF M).choose
      let snf : Module.Basis.SmithNormalForm
          (LinearMap.range (Matrix.toLin' M)) ι n :=
        (hSNF M).choose_spec.some
      if h : ∃ j : Fin n, snf.f j = i then snf.a h.choose else 0, ?_⟩
  intro M
  set n := (hSNF M).choose
  set snf : Module.Basis.SmithNormalForm
      (LinearMap.range (Matrix.toLin' M)) ι n :=
    (hSNF M).choose_spec.some
  refine ⟨n, snf, ?_, ?_⟩
  · intro j
    dsimp only
    have hex : ∃ j' : Fin n, snf.f j' = snf.f j := ⟨j, rfl⟩
    have hpos :
        (if h : ∃ j' : Fin n, snf.f j' = snf.f j then snf.a h.choose else 0) =
          snf.a hex.choose := dif_pos hex
    rw [hpos]
    congr 1
    exact snf.f.injective hex.choose_spec
  · intro i hi
    dsimp only
    exact dif_neg fun h => hi h.choose h.choose_spec
