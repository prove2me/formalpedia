-- Prove2me | solution 1 for QAlgorithms.Nannicini.basisState_iff_prod_basisStates
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T21:00:05.766107+00:00
-- url     : https://prove2.me/submissions/654ba4c8-c474-4ec9-9c52-8c591317adab

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

open QAlgorithms
open scoped BigOperators





/-- Nannicini p.14, Proposition 1.19: a `q`-qubit register, `q > 1`, is in a basis state
(Def. 1.16: `|ψ⟩ = α_k |k⟩` with `|α_k|² = 1`) if and only if its state is the tensor product
`|ψ_1⟩ ⊗ ⋯ ⊗ |ψ_q⟩` of `q` single-qubit states each of which is a basis state. Wire `i` is the
source's qubit `i + 1` (the first qubit is the most significant). -/
theorem solution {q : ℕ} (hq : 1 < q)
    (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ) :
    IsBasisState ψ ↔ ∃ φ : Fin q → EuclideanSpace ℂ Bool,
      (∀ i, IsState (φ i) ∧ IsBasisState (φ i)) ∧ ψ = prodState φ := by
  classical
  have hp (k : Qubits q) (a : Fin q → ℂ) :
      prodState (fun i => a i • ket (k i)) = (∏ i, a i) • ket k := by
    ext z
    change (∏ i, a i * (ket (k i)) (z i)) = (∏ i, a i) * (ket k) z
    simp only [ket, EuclideanSpace.single_apply]
    by_cases hz : z = k
    · subst z
      simp
    · have hn : ¬ ∀ i, z i = k i := by
        intro h
        exact hz (funext h)
      obtain ⟨i, hi⟩ := not_forall.mp hn
      rw [if_neg hz, mul_zero]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  constructor
  · rintro ⟨k, a, ha, rfl⟩
    let i0 : Fin q := ⟨0, by omega⟩
    let w : Fin q → ℂ := fun i => if i = i0 then a else 1
    have hw : ∀ i, ‖w i‖ = 1 := by
      intro i
      by_cases h : i = i0 <;> simp [w, h, ha]
    refine ⟨fun i => w i • ket (k i), ?_, ?_⟩
    · intro i
      constructor
      · simp [IsState, norm_smul, ket, EuclideanSpace.norm_single, hw]
      · exact ⟨k i, w i, hw i, rfl⟩
    · rw [hp]
      have hprod : (∏ i, w i) = a := by
        simp [w, Finset.prod_ite_eq']
      rw [hprod]
  · rintro ⟨φ, hφ, rfl⟩
    have hb : ∀ i, ∃ k : Bool, ∃ a : ℂ, ‖a‖ = 1 ∧ φ i = a • ket k :=
      fun i => (hφ i).2
    choose k a ha he using hb
    have heq : φ = fun i => a i • ket (k i) := funext he
    rw [heq, hp]
    refine ⟨k, ∏ i, a i, ?_, rfl⟩
    simp [norm_prod, ha]
