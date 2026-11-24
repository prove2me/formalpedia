-- Prove2me | solution 2 for WeilConjectures.exists_mapped_bases_of_on_range_and_ker
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T05:02:56.046669+00:00
-- url     : https://prove2.me/submissions/bdd2cc0f-7d17-4284-b66e-cb526c8391a0

import Mathlib

/-- Counterexample: the zero diagonal assignment `d ≡ 0` with no on-range indices
satisfies the on-range hypothesis for every matrix, but for `M = 1` on a one-point
index type a source basis would have to consist of zero vectors. -/
theorem solution :
    ¬ (∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
      (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
      (hon : ∀ (M : Matrix ι ι (Polynomial K)), ∃ (n : ℕ) (e : Fin n ↪ ι)
        (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
        (v : Fin n → (ι → Polynomial K)),
        (∀ j, Matrix.toLin' M (v j) = d M (e j) • bTgt (e j)) ∧
          (∀ i, (∀ j : Fin n, e j ≠ i) → d M i = 0))
      (_hker : ∀ (M : Matrix ι ι (Polynomial K)),
        Module.Free (Polynomial K) (LinearMap.ker (Matrix.toLin' M)) ∧
          Module.Finite (Polynomial K) (LinearMap.ker (Matrix.toLin' M))),
      ∀ (M : Matrix ι ι (Polynomial K)),
        ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
          ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i) := by
  intro h
  have hon : ∀ (M : Matrix Unit Unit (Polynomial ℚ)), ∃ (n : ℕ) (e : Fin n ↪ Unit)
      (bTgt : Module.Basis Unit (Polynomial ℚ) (Unit → Polynomial ℚ))
      (v : Fin n → (Unit → Polynomial ℚ)),
      (∀ j, Matrix.toLin' M (v j) = (0 : Unit → Polynomial ℚ) (e j) • bTgt (e j)) ∧
        (∀ i, (∀ j : Fin n, e j ≠ i) → (0 : Unit → Polynomial ℚ) i = 0) :=
    fun _ => ⟨0, Function.Embedding.ofIsEmpty, Pi.basisFun _ _, fun j => j.elim0,
      fun j => j.elim0, fun _ _ => rfl⟩
  have hker : ∀ (M : Matrix Unit Unit (Polynomial ℚ)),
      Module.Free (Polynomial ℚ) (LinearMap.ker (Matrix.toLin' M)) ∧
        Module.Finite (Polynomial ℚ) (LinearMap.ker (Matrix.toLin' M)) :=
    fun _ => ⟨inferInstance, inferInstance⟩
  obtain ⟨bSrc, _bTgt, hb⟩ := h (K := ℚ) (ι := Unit) (fun _ => 0) hon hker 1
  have h0 : bSrc () = 0 := by
    have := hb ()
    simpa [Matrix.toLin'_one] using this
  exact bSrc.ne_zero () h0
