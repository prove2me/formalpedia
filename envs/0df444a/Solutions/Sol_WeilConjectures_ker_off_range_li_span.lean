-- Prove2me | solution 1 for WeilConjectures.ker_off_range_li_span
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T04:55:27.725914+00:00
-- url     : https://prove2.me/submissions/875ed384-3dd1-4dfd-b231-65d65de8b713

import Mathlib

/-- Counterexample: `M = 1`, `d = 0`, `f = 0`, no on-range indices (`n = 0`), over a
one-point index type. Every hypothesis holds, but the zero family is not linearly
independent. -/
theorem solution :
    ¬ (∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
      (M : Matrix ι ι (Polynomial K))
      (d : ι → Polynomial K)
      {n : ℕ} (e : Fin n ↪ ι)
      (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
      (v : Fin n → (ι → Polynomial K))
      {m : ℕ}
      (bKer : Module.Basis (Fin m) (Polynomial K)
        (LinearMap.ker (Matrix.toLin' M)))
      (f : ι → (ι → Polynomial K))
      (hmap : ∀ i, Matrix.toLin' M (f i) = d i • bTgt i)
      (hon : ∀ j, f (e j) = v j)
      (hker : ∀ i, (∀ j : Fin n, e j ≠ i) →
        f i ∈ LinearMap.ker (Matrix.toLin' M)),
      LinearIndependent (Polynomial K) f ∧
        ⊤ ≤ Submodule.span (Polynomial K) (Set.range f)) := by
  intro h
  -- the kernel of the identity is trivial, so it has the empty basis
  have hsub : Subsingleton (LinearMap.ker (Matrix.toLin'
      (1 : Matrix PUnit PUnit (Polynomial (ℚ))))) := by
    rw [Matrix.toLin'_one, LinearMap.ker_id]
    infer_instance
  let bKer : Module.Basis (Fin 0) (Polynomial (ℚ))
      (LinearMap.ker (Matrix.toLin'
        (1 : Matrix PUnit PUnit (Polynomial (ℚ))))) := Module.Basis.empty _
  have hli := (h (K := ℚ) (ι := PUnit)
    (1 : Matrix PUnit PUnit (Polynomial (ℚ))) 0 (n := 0)
    (Function.Embedding.ofIsEmpty) (Pi.basisFun _ _) (fun j => j.elim0) bKer 0
    (by intro i; simp) (fun j => j.elim0)
    (fun i _ => Submodule.zero_mem _)).1
  exact hli.ne_zero PUnit.unit rfl
