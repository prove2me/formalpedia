-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P05.split_central_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:18:05.330252+00:00
-- url     : https://prove2.me/submissions/7ba23486-859a-40e4-a9d6-d08a3c5c525d

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05
noncomputable section
open QAlgorithms.Papers.Independent.Support21.P05
open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

def g66c_fst (a : E6Central) : Sl3 :=
  ⟨Matrix.of (fun i j => (a.val i j).1), by
    have h : Matrix.trace a.val = 0 := a.2
    show Matrix.trace (Matrix.of fun i j => (a.val i j).1) = 0
    have := congrArg Prod.fst h
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Prod.fst_sum] at this ⊢
    simpa using this⟩

def g66c_snd (a : E6Central) : Sl3 :=
  ⟨Matrix.of (fun i j => (a.val i j).2), by
    have h : Matrix.trace a.val = 0 := a.2
    show Matrix.trace (Matrix.of fun i j => (a.val i j).2) = 0
    have := congrArg Prod.snd h
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Prod.snd_sum] at this ⊢
    simpa using this⟩

def g66c_join (p : Sl3 × Sl3) : E6Central :=
  ⟨splitJoin p.1.val p.2.val, by
    have h1 := p.1.2
    have h2 := p.2.2
    simp only [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at h1 h2 ⊢
    simp only [Matrix.trace, splitJoin, Matrix.diag] at h1 h2 ⊢
    refine Prod.ext ?_ ?_
    · simpa [Prod.fst_sum] using h1
    · simpa [Prod.snd_sum] using h2⟩

def g66c_e : E6Central ≃ₗ[ℂ] (Sl3 × Sl3) where
  toFun a := (g66c_fst a, g66c_snd a)
  invFun := g66c_join
  map_add' a b := rfl
  map_smul' r a := rfl
  left_inv a := by
    apply Subtype.ext; ext i j <;> rfl
  right_inv p := rfl

theorem solution :
    ∃ e : E6Central ≃ₗ[ℂ] (Sl3 × Sl3),
      (∀ a, (e a).1.val = (fun i j => (a.val i j).1) ∧
        (e a).2.val = (fun i j => (a.val i j).2) ∧
        a.val = splitJoin (e a).1.val 0 + splitJoin 0 (e a).2.val) ∧
      (∀ a b, matrixComm a.val b.val =
        splitJoin (matrixComm (e a).1.val (e b).1.val)
          (matrixComm (e a).2.val (e b).2.val)) ∧
      (∀ a b : Sl3, matrixComm (splitJoin a.val 0) (splitJoin 0 b.val) = 0) := by
  refine ⟨g66c_e, fun a => ⟨rfl, rfl, ?_⟩, fun a b => ?_, fun a b => ?_⟩
  · ext i j <;> simp [splitJoin, g66c_e, g66c_fst, g66c_snd]
  · ext i j <;>
      simp [matrixComm, splitJoin, g66c_e, g66c_fst, g66c_snd, Matrix.mul_apply, Prod.fst_sum,
        Prod.snd_sum] <;> rfl
  · ext i j <;>
      simp [matrixComm, splitJoin, Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum]

end
