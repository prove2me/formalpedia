-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P34.finite_unitarity_equivariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:17:07.482657+00:00
-- url     : https://prove2.me/submissions/99d2bdc6-604a-4f47-a398-fb920c4c4756

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P34

def g68i_e1 (n m : ℕ) : (Fin n × Fin m × Fin m × Fin n) ≃ (Fin n × Fin n × Fin m × Fin m) where
  toFun p := (p.1, p.2.2.2, p.2.2.1, p.2.1)
  invFun q := (q.1, q.2.2.2, q.2.2.1, q.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def g68i_e2 (n m : ℕ) : (Fin n × Fin m × Fin m × Fin n) ≃ (Fin n × Fin n × Fin m × Fin m) where
  toFun p := (p.1, p.2.2.2, p.2.1, p.2.2.1)
  invFun q := (q.1, q.2.2.1, q.2.2.2, q.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem g68i_J_apply {n m : ℕ} (v : FourTensor n n m m) (p : Fin n × Fin m × Fin m × Fin n) :
    jamiolkowskiTensor v p = v (g68i_e1 n m p) := rfl

theorem g68i_T_apply {n m : ℕ} (v : FourTensor n n m m) (p : Fin n × Fin m × Fin m × Fin n) :
    twistedJamiolkowski v p = v (g68i_e2 n m p) := rfl

theorem g68i_bij {n m : ℕ} (L : FourTensor n n m m →ₗ[ℂ] FourTensor n m m n)
    (e : (Fin n × Fin m × Fin m × Fin n) ≃ (Fin n × Fin n × Fin m × Fin m))
    (h : ∀ v p, L v p = v (e p)) : Function.Bijective L := by
  constructor
  · intro v w hvw
    ext q
    have := congrArg (fun u : FourTensor n m m n => u (e.symm q)) hvw
    simpa [h] using this
  · intro u
    refine ⟨WithLp.toLp 2 (fun q => u (e.symm q)), ?_⟩
    ext p
    rw [h]
    simp

theorem g68i_inner {n m : ℕ} (L : FourTensor n n m m →ₗ[ℂ] FourTensor n m m n)
    (e : (Fin n × Fin m × Fin m × Fin n) ≃ (Fin n × Fin n × Fin m × Fin m))
    (h : ∀ v p, L v p = v (e p)) (v w : FourTensor n n m m) :
    inner ℂ (L v) (L w) = inner ℂ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Fintype.sum_equiv e _ _ (fun p => by rw [h, h])

theorem solution (n m : ℕ) :
    Function.Bijective (jamiolkowskiTensor (n := n) (m := m)) ∧
    Function.Bijective (twistedJamiolkowski (n := n) (m := m)) ∧
    (∀ v w : FourTensor n n m m,
      inner ℂ (jamiolkowskiTensor v) (jamiolkowskiTensor w) = inner ℂ v w ∧
      inner ℂ (twistedJamiolkowski v) (twistedJamiolkowski w) = inner ℂ v w) ∧
    (∀ (A Aprime : (Matrix (Fin n) (Fin n) ℂ)ˣ)
        (B Bprime : (Matrix (Fin m) (Fin m) ℂ)ˣ) (v : FourTensor n n m m),
      jamiolkowskiTensor
          (factorAction A.val (dualMatrix Aprime.val) B.val (dualMatrix Bprime.val) v) =
        factorAction A.val (dualMatrix Bprime.val) B.val (dualMatrix Aprime.val)
          (jamiolkowskiTensor v) ∧
      twistedJamiolkowski
          (factorAction A.val (dualMatrix Aprime.val) B.val (dualMatrix Bprime.val) v) =
        factorAction A.val B.val (dualMatrix Bprime.val) (dualMatrix Aprime.val)
          (twistedJamiolkowski v)) := by
  refine ⟨g68i_bij _ _ g68i_J_apply, g68i_bij _ _ g68i_T_apply,
    fun v w => ⟨g68i_inner _ _ g68i_J_apply v w, g68i_inner _ _ g68i_T_apply v w⟩, ?_⟩
  intro A Aprime B Bprime v
  constructor
  · ext p
    rw [g68i_J_apply]
    simp only [factorAction, PiLp.toLp_apply]
    refine (Fintype.sum_equiv (g68i_e1 n m) _ _ (fun r => ?_)).symm
    rw [g68i_J_apply]
    simp only [g68i_e1, Equiv.coe_fn_mk]
    ring
  · ext p
    rw [g68i_T_apply]
    simp only [factorAction, PiLp.toLp_apply]
    refine (Fintype.sum_equiv (g68i_e2 n m) _ _ (fun r => ?_)).symm
    rw [g68i_T_apply]
    simp only [g68i_e2, Equiv.coe_fn_mk]
    ring
