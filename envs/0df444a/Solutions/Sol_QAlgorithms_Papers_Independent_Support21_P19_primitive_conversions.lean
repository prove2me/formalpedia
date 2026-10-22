-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.primitive_conversions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:24:51.617992+00:00
-- url     : https://prove2.me/submissions/1c947635-906f-4ecb-baa2-7f80d1cf6421

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19
attribute [local instance] Classical.propDecidable Classical.decEq

lemma g67b_chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (V : Matrix κ ι ℂ) (h : Vᴴ * V = 1) : IsChannel (conjSuperop V) :=
  ⟨1, fun _ => V, by simp [IsKrausFamily, h], fun ρ => by simp [krausApply, conjSuperop]⟩

lemma g67b_chan_id {ι : Type*} [Fintype ι] [DecidableEq ι] : IsChannel (fun M : Matrix ι ι ℂ => M) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

@[simp] lemma g67b_sj {a b : ℕ} (x : Fin a) (y : Fin b) : split (joinRegisters x y) = (x,y) :=
  finProdFinEquiv.symm_apply_apply (x,y)

@[simp] lemma g67b_jinj {a b : ℕ} (x x' : Fin a) (y y' : Fin b) :
    joinRegisters x y = joinRegisters x' y' ↔ x = x' ∧ y = y' := by
  unfold joinRegisters; rw [finProdFinEquiv.apply_eq_iff_eq]; simp

lemma g67b_sum {a b : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (a*b) → M) :
    ∑ k, f k = ∑ x : Fin a, ∑ y : Fin b, f (joinRegisters x y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv (fun p => f (finProdFinEquiv p)) f (fun p => rfl)).symm

lemma g67b_ex {a b : ℕ} (k : Fin (a*b)) : ∃ x y, k = joinRegisters x y :=
  ⟨(split k).1, (split k).2, (finProdFinEquiv.apply_symm_apply k).symm⟩

@[simp] lemma g67b_join1 (x : Fin 1) (i : Fin 2) : joinRegisters (a := 1) (b := 2) x i = i := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp [Fin.fin_one_eq_zero x]

@[simp] lemma g67b_join2 (x : Fin 1) (i : Fin 2) : joinRegisters (a := 2) (b := 1) i x = i := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp [Fin.fin_one_eq_zero x]

@[simp] lemma g67b_split1 (i : Fin 2) : split (a := 1) (b := 2) i = (0, i) := by
  unfold split; rw [Equiv.symm_apply_eq]; exact (g67b_join1 0 i).symm

@[simp] lemma g67b_split2 (i : Fin 2) : split (a := 2) (b := 1) i = (i, 0) := by
  unfold split; rw [Equiv.symm_apply_eq]; exact (g67b_join2 0 i).symm

@[simp] lemma g67b_j11 : joinRegisters (a := 1) (b := 1) (0 : Fin 1) (0 : Fin 1) = 0 := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp

lemma g67b_seq_eq {D : Type} {L : Kind → Resource} {a b c d : ℕ} {v : Kind → ℕ}
    {F G : D → Superop (Fin a × Fin b) (Fin c × Fin d)} (h : Sequential L a b c d v F) (e : F = G) :
    Sequential L a b c d v G := e ▸ h

def g67b_copy : Matrix (Fin (2*2)) (Fin 2) ℂ := fun k z => if (split k).1 = z ∧ (split k).2 = z then 1 else 0

lemma g67b_copy_iso : g67b_copyᴴ * g67b_copy = 1 := by
  ext a b
  rw [Matrix.mul_apply, g67b_sum]
  fin_cases a <;> fin_cases b <;> simp [g67b_copy, Fin.sum_univ_succ, Matrix.conjTranspose_apply]

def g67b_qext (M : Matrix (Fin (2*2) × Fin 1) (Fin (2*2) × Fin 1) ℂ) :
    Matrix (Fin (1*2) × Fin (2*1)) (Fin (1*2) × Fin (2*1)) ℂ := fun i j =>
  M (joinRegisters (split i.2).1 (split i.1).2, joinRegisters (0 : Fin 1) (split i.2).2)
    (joinRegisters (split j.2).1 (split j.1).2, joinRegisters (0 : Fin 1) (split j.2).2)

lemma g67b_qext_eq : extend (library (qubitChannel 2) Kind.main) 2 1 = g67b_qext := rfl

lemma g67b_qubit_cobit : Exact (qubitChannel 2) (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) := by
  have s1 := Sequential.localStep (L := library (qubitChannel 2)) (D := Unit) (fun _ => conjSuperop g67b_copy)
    (fun M : Matrix (Fin 1) (Fin 1) ℂ => M) (fun _ => g67b_chan_conj _ g67b_copy_iso) g67b_chan_id
  have s2 := Sequential.callStep (L := library (qubitChannel 2)) (D := Unit) Kind.main 2 1
  have s := Sequential.compose s1 s2
  refine ⟨fun k => 0 + oneCall Kind.main k, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · rw [g67b_qext_eq] at s
    have key : ∀ (M : Matrix (Fin 2 × Fin (1*1)) (Fin 2 × Fin (1*1)) ℂ) (i j : Fin 2 × Fin 2),
        g67b_qext (localMap (conjSuperop g67b_copy) (fun M : Matrix (Fin 1) (Fin 1) ℂ => M) M) i j
          = if i.1 = i.2 ∧ j.1 = j.2 then M (i.1, 0) (j.1, 0) else 0 := by
      intro M i j
      simp only [g67b_qext, localMap, conjSuperop, g67b_split1, g67b_split2]
      rcases i with ⟨a, b⟩; rcases j with ⟨c, d⟩
      simp only [Matrix.mul_apply, g67b_sum, Matrix.conjTranspose_apply, g67b_copy, g67b_sj]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [Fin.sum_univ_succ, Matrix.mul_apply, g67b_j11]
      all_goals (erw [Matrix.mul_apply]; simp [Fin.sum_univ_succ, g67b_copy])

    exact g67b_seq_eq s (funext fun _ => funext fun M => funext fun i => funext fun j => key M i j)

def g67b_trK : Fin 2 → Matrix (Fin 1) (Fin (2*1)) ℂ := fun k _ u => if u = joinRegisters k (0 : Fin 1) then 1 else 0

lemma g67b_trK_kraus : IsKrausFamily g67b_trK := by
  unfold IsKrausFamily
  ext a b
  obtain ⟨x, y, rfl⟩ := g67b_ex a
  obtain ⟨x', y', rfl⟩ := g67b_ex b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g67b_trK, Matrix.one_apply]
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;> simp [Fin.sum_univ_succ]

def g67b_cext (M : Matrix (Fin (2*1) × Fin (1*1)) (Fin (2*1) × Fin (1*1)) ℂ) :
    Matrix (Fin (2*1) × Fin (2*1)) (Fin (2*1) × Fin (2*1)) ℂ := fun i j =>
  if (split i.1).1 = (split i.2).1 ∧ (split j.1).1 = (split j.2).1 then
    M (joinRegisters (split i.1).1 (split i.1).2, joinRegisters (0 : Fin 1) (split i.2).2)
      (joinRegisters (split j.1).1 (split j.1).2, joinRegisters (0 : Fin 1) (split j.2).2) else 0

lemma g67b_cext_eq : extend (library (cobitChannel 2) Kind.main) 1 1 = g67b_cext := rfl

lemma g67b_cobit_cbit : Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (cbitChannel 2) := by
  have s1 := Sequential.callStep (L := library (cobitChannel 2)) (D := Unit) Kind.main 1 1
  have s2 := Sequential.localStep (L := library (cobitChannel 2)) (D := Unit) (fun _ => krausApply g67b_trK)
    (fun M : Matrix (Fin (2*1)) (Fin (2*1)) ℂ => M) (fun _ => ⟨2, g67b_trK, g67b_trK_kraus, fun _ => rfl⟩) g67b_chan_id
  have s := Sequential.compose s1 s2
  refine ⟨fun k => oneCall Kind.main k + 0, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · rw [g67b_cext_eq] at s
    have key : ∀ (M : Matrix (Fin (2*1) × Fin (1*1)) (Fin (2*1) × Fin (1*1)) ℂ) (i j : Fin 1 × Fin (2*1)),
        localMap (krausApply g67b_trK) (fun M : Matrix (Fin (2*1)) (Fin (2*1)) ℂ => M) (g67b_cext M) i j
          = if i.2 = j.2 then M (i.2, 0) (j.2, 0) else 0 := by
      intro M i j
      rcases i with ⟨a, b⟩; rcases j with ⟨c, d⟩
      obtain ⟨b1, b2, rfl⟩ := g67b_ex b
      obtain ⟨d1, d2, rfl⟩ := g67b_ex d
      simp only [localMap, krausApply, g67b_cext, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        g67b_trK, g67b_sj]
      fin_cases a; fin_cases c
      fin_cases b1 <;> fin_cases b2 <;> fin_cases d1 <;> fin_cases d2 <;> simp [Fin.sum_univ_succ, g67b_sum]
      all_goals (erw [Matrix.mul_apply, Matrix.mul_apply]; simp [g67b_sum, g67b_trK])
    exact g67b_seq_eq s (funext fun _ => funext fun M => funext fun i => funext fun j => key M i j)

def g67b_plus : Matrix (Fin (2*1)) (Fin 1) ℂ := fun _ _ => ((Real.sqrt 2)⁻¹ : ℂ)

lemma g67b_plus_iso : g67b_plusᴴ * g67b_plus = 1 := by
  ext a b
  rw [Matrix.mul_apply, g67b_sum]
  fin_cases a; fin_cases b
  simp [g67b_plus, Fin.sum_univ_succ, Matrix.conjTranspose_apply]
  have h : ((Real.sqrt 2 : ℂ))⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [h]; norm_num

lemma g67b_cobit_ebit : Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (entangled 2) := by
  have s1 := Sequential.localStep (L := library (cobitChannel 2)) (D := Unit) (fun _ => conjSuperop g67b_plus)
    (fun M : Matrix (Fin 1) (Fin 1) ℂ => M) (fun _ => g67b_chan_conj _ g67b_plus_iso) g67b_chan_id
  have s2 := Sequential.callStep (L := library (cobitChannel 2)) (D := Unit) Kind.main 1 1
  have s := Sequential.compose s1 s2
  refine ⟨fun k => 0 + oneCall Kind.main k, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · rw [g67b_cext_eq] at s
    have key : ∀ (M : Matrix (Fin 1 × Fin (1*1)) (Fin 1 × Fin (1*1)) ℂ) (i j : Fin (2*1) × Fin (2*1)),
        g67b_cext (localMap (conjSuperop g67b_plus) (fun M : Matrix (Fin 1) (Fin 1) ℂ => M) M) i j
          = M (0, 0) (0, 0) * pureDensity (maximallyEntangledKet 2) i j := by
      intro M i j
      rcases i with ⟨a, b⟩; rcases j with ⟨c, d⟩
      obtain ⟨a1, a2, rfl⟩ := g67b_ex a
      obtain ⟨b1, b2, rfl⟩ := g67b_ex b
      obtain ⟨c1, c2, rfl⟩ := g67b_ex c
      obtain ⟨d1, d2, rfl⟩ := g67b_ex d
      simp only [localMap, conjSuperop, g67b_cext, g67b_sj, pureDensity, maximallyEntangledKet,
        finiteMaxEntangled]
      fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2 <;>
        fin_cases d1 <;> fin_cases d2 <;> simp [Matrix.mul_apply, g67b_plus, Matrix.conjTranspose_apply]
      all_goals (erw [Matrix.mul_apply]; simp [g67b_plus]; ring)
    exact g67b_seq_eq s (funext fun _ => funext fun M => funext fun i => funext fun j => key M i j)

/-- PDF pp.1–2: three separate primitive conversions, with zero borrowed EPR pairs. -/
theorem solution :
    Exact (qubitChannel 2) (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) ∧
    Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (cbitChannel 2) ∧
    Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (entangled 2) :=
  ⟨g67b_qubit_cobit, g67b_cobit_cbit, g67b_cobit_ebit⟩
