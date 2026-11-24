-- Prove2me | solution 2 for WeilConjectures.exists_mapped_bases_of_on_range_src_and_ker_basis
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T04:59:44.122811+00:00
-- url     : https://prove2.me/submissions/01720e58-f118-4933-92d1-31bf399d7426

import Mathlib

/-- Counterexample: `M = 1`, `d = 0`, no on-range indices, one-point index type.
A basis `bSrc` with `toLin' 1 (bSrc i) = 0` would consist of zero vectors. -/
theorem solution :
    ¬ (∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
      (M : Matrix ι ι (Polynomial K))
      (d : ι → Polynomial K)
      {n : ℕ} (e : Fin n ↪ ι)
      (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
      (v : Fin n → (ι → Polynomial K))
      (hv : ∀ j, Matrix.toLin' M (v j) = d (e j) • bTgt (e j))
      (hoff : ∀ i, (∀ j : Fin n, e j ≠ i) → d i = 0)
      {m : ℕ}
      (_bKer : Module.Basis (Fin m) (Polynomial K)
        (LinearMap.ker (Matrix.toLin' M))),
      ∃ (bSrc : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        ∀ i, Matrix.toLin' M (bSrc i) = d i • bTgt i) := by
  intro h
  have hsub : Subsingleton (LinearMap.ker (Matrix.toLin'
      (1 : Matrix PUnit PUnit (Polynomial ℚ)))) := by
    rw [Matrix.toLin'_one, LinearMap.ker_id]
    infer_instance
  let bKer : Module.Basis (Fin 0) (Polynomial ℚ)
      (LinearMap.ker (Matrix.toLin'
        (1 : Matrix PUnit PUnit (Polynomial ℚ)))) := Module.Basis.empty _
  obtain ⟨bSrc, hb⟩ := h (K := ℚ) (ι := PUnit)
    (1 : Matrix PUnit PUnit (Polynomial ℚ)) 0 (n := 0)
    (Function.Embedding.ofIsEmpty) (Pi.basisFun _ _) (fun j => j.elim0)
    (fun j => j.elim0) (fun _ _ => rfl) bKer
  have h0 : bSrc PUnit.unit = 0 := by
    have := hb PUnit.unit
    simpa [Matrix.toLin'_one] using this
  exact bSrc.ne_zero PUnit.unit h0
