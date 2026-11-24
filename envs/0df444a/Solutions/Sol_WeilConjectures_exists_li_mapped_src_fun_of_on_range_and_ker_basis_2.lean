-- Prove2me | solution 2 for WeilConjectures.exists_li_mapped_src_fun_of_on_range_and_ker_basis
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T04:58:27.659801+00:00
-- url     : https://prove2.me/submissions/6a8b9fd3-7e93-441f-9a7a-4cc2460b0e8d

import Mathlib

/-- Counterexample: `M = 1`, `d = 0`, no on-range indices, one-point index type.
Any `f` with `toLin' 1 (f i) = 0` is the zero family, which is not linearly independent. -/
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
      (bKer : Module.Basis (Fin m) (Polynomial K)
        (LinearMap.ker (Matrix.toLin' M))),
      ∃ (f : ι → (ι → Polynomial K)),
        (∀ i, Matrix.toLin' M (f i) = d i • bTgt i) ∧
          LinearIndependent (Polynomial K) f ∧
            ⊤ ≤ Submodule.span (Polynomial K) (Set.range f)) := by
  intro h
  have hsub : Subsingleton (LinearMap.ker (Matrix.toLin'
      (1 : Matrix PUnit PUnit (Polynomial ℚ)))) := by
    rw [Matrix.toLin'_one, LinearMap.ker_id]
    infer_instance
  let bKer : Module.Basis (Fin 0) (Polynomial ℚ)
      (LinearMap.ker (Matrix.toLin'
        (1 : Matrix PUnit PUnit (Polynomial ℚ)))) := Module.Basis.empty _
  obtain ⟨f, hf, hli, -⟩ := h (K := ℚ) (ι := PUnit)
    (1 : Matrix PUnit PUnit (Polynomial ℚ)) 0 (n := 0)
    (Function.Embedding.ofIsEmpty) (Pi.basisFun _ _) (fun j => j.elim0)
    (fun j => j.elim0) (fun _ _ => rfl) bKer
  have h0 : f PUnit.unit = 0 := by
    have := hf PUnit.unit
    simpa [Matrix.toLin'_one] using this
  exact hli.ne_zero PUnit.unit h0
