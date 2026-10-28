-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P37.exact_cbit_ebit_cobit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:06:44.979053+00:00
-- url     : https://prove2.me/submissions/a21e4f79-365c-4d2d-a5f6-437c6cb9313f

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19
attribute [local instance] Classical.propDecidable Classical.decEq

lemma g69_chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (V : Matrix κ ι ℂ) (h : Vᴴ * V = 1) : IsChannel (conjSuperop V) :=
  ⟨1, fun _ => V, by simp [IsKrausFamily, h], fun ρ => by simp [krausApply, conjSuperop]⟩

lemma g69_chan_id {ι : Type*} [Fintype ι] [DecidableEq ι] : IsChannel (fun M : Matrix ι ι ℂ => M) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

@[simp] lemma g69_sj {a b : ℕ} (x : Fin a) (y : Fin b) : split (joinRegisters x y) = (x,y) :=
  finProdFinEquiv.symm_apply_apply (x,y)

@[simp] lemma g69_jinj {a b : ℕ} (x x' : Fin a) (y y' : Fin b) :
    joinRegisters x y = joinRegisters x' y' ↔ x = x' ∧ y = y' := by
  unfold joinRegisters; rw [finProdFinEquiv.apply_eq_iff_eq]; simp

lemma g69_sum {a b : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (a*b) → M) :
    ∑ k, f k = ∑ x : Fin a, ∑ y : Fin b, f (joinRegisters x y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv (fun p => f (finProdFinEquiv p)) f (fun p => rfl)).symm

lemma g69_ex {a b : ℕ} (k : Fin (a*b)) : ∃ x y, k = joinRegisters x y :=
  ⟨(split k).1, (split k).2, (finProdFinEquiv.apply_symm_apply k).symm⟩

@[simp] lemma g69_join1 (x : Fin 1) (i : Fin 2) : joinRegisters (a := 1) (b := 2) x i = i := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp [Fin.fin_one_eq_zero x]

@[simp] lemma g69_join2 (x : Fin 1) (i : Fin 2) : joinRegisters (a := 2) (b := 1) i x = i := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp [Fin.fin_one_eq_zero x]

@[simp] lemma g69_split1 (i : Fin 2) : split (a := 1) (b := 2) i = (0, i) := by
  unfold split; rw [Equiv.symm_apply_eq]; exact (g69_join1 0 i).symm

@[simp] lemma g69_split2 (i : Fin 2) : split (a := 2) (b := 1) i = (i, 0) := by
  unfold split; rw [Equiv.symm_apply_eq]; exact (g69_join2 0 i).symm

@[simp] lemma g69_j11 : joinRegisters (a := 1) (b := 1) (0 : Fin 1) (0 : Fin 1) = 0 := by
  ext; rw [joinRegisters, finProdFinEquiv_apply_val]; simp

@[simp] lemma g69_split11 (i : Fin 1) : split (a := 1) (b := 1) i = (0, 0) := by
  ext <;> simp [Fin.fin_one_eq_zero]

lemma g69_seq_eq {D : Type} {L : Kind → Resource} {a b c d : ℕ} {v : Kind → ℕ}
    {F G : D → Superop (Fin a × Fin b) (Fin c × Fin d)} (h : Sequential L a b c d v F) (e : F = G) :
    Sequential L a b c d v G := e ▸ h

/-- permutation matrix of an involution `f`. -/
def g69_perm {n : ℕ} (f : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℂ := fun k l => if l = f k then 1 else 0

lemma g69_perm_conj {n : ℕ} (f : Fin n → Fin n) (N : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) :
    conjSuperop (g69_perm f) N k l = N (f k) (f l) := by
  simp [conjSuperop, g69_perm, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma g69_perm_iso {n : ℕ} (f : Fin n → Fin n) (hf : ∀ k, f (f k) = k) :
    (g69_perm f)ᴴ * g69_perm f = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g69_perm, Matrix.one_apply]
  have hinj : ∀ x y, f x = f y → x = y := fun x y h => by rw [← hf x, h, hf y]
  by_cases hab : a = b
  · subst hab; simp only [if_true]
    rw [Finset.sum_eq_single (f a)]
    · simp [hf]
    · intro x _ hx; have : ¬ a = f x := fun h => hx (by rw [h, hf]); simp [this]
    · simp
  · simp only [hab, if_false]
    apply Finset.sum_eq_zero; intro x _
    by_cases h1 : a = f x <;> by_cases h2 : b = f x <;> simp [h1, h2]
    exact hab (h1.trans h2.symm)

/-- CNOT on Alice's (ebit half, input) register. -/
def g69_cn : Fin (2*2) → Fin (2*2) := fun k => joinRegisters ((split k).1 + (split k).2) (split k).2

lemma g69_cn_inv (k : Fin (2*2)) : g69_cn (g69_cn k) = k := by
  obtain ⟨x, y, rfl⟩ := g69_ex k
  simp only [g69_cn, g69_sj]
  congr 1; fin_cases x <;> fin_cases y <;> rfl

@[simp] lemma g69_cn_join (x y : Fin 2) : g69_cn (joinRegisters x y) = joinRegisters (x + y) y := by
  simp [g69_cn]

/-- Bob's correction: from (message m, ebit half b) output b + m. -/
def g69_K : Fin 2 → Matrix (Fin 2) (Fin (2*2)) ℂ := fun m z k =>
  if k = joinRegisters m (z + m) then 1 else 0

lemma g69_K_kraus : IsKrausFamily g69_K := by
  unfold IsKrausFamily
  ext a b
  obtain ⟨x, y, rfl⟩ := g69_ex a
  obtain ⟨x', y', rfl⟩ := g69_ex b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g69_K, Matrix.one_apply,
    g69_jinj]
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;> simp [Fin.sum_univ_succ] <;> decide

lemma g69_K_apply (N : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) (z z' : Fin 2) :
    krausApply g69_K N z z' = ∑ m : Fin 2, N (joinRegisters m (z + m)) (joinRegisters m (z' + m)) := by
  simp [krausApply, g69_K, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma g69_h2 : ((Real.sqrt 2 : ℂ))⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem g69_forward : Exact (idle 1 1) (budget 0 1 0 0 0 0 1 0) (cobitChannel 2) := by
  have s1 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.ebit 2 1
  have s2 := Sequential.localStep (L := library (idle 1 1)) (D := Unit)
    (fun _ => conjSuperop (g69_perm g69_cn))
    (fun M => M : Superop (Fin (2*1)) (Fin (1*2)))
    (fun _ => g69_chan_conj _ (g69_perm_iso _ g69_cn_inv)) (g69_chan_id (ι := Fin 2))
  have s3 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.cbitF 2 2
  have s4 := Sequential.localStep (L := library (idle 1 1)) (D := Unit)
    (fun _ => (fun M => M : Superop (Fin (1*2)) (Fin 2)))
    (krausApply g69_K) (fun _ => g69_chan_id (ι := Fin 2)) ⟨2, g69_K, g69_K_kraus, fun _ => rfl⟩
  have s := Sequential.compose (Sequential.compose (Sequential.compose s1 s2) s3) s4
  refine ⟨_, ?_, g69_seq_eq s ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have key : ∀ (M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (i j : Fin 2 × Fin 2),
        localMap (fun M => M) (krausApply g69_K) (extend (library (idle 1 1) Kind.cbitF) 2 2
          (localMap (conjSuperop (g69_perm g69_cn)) (fun M => M : Superop (Fin (2*1)) (Fin (1*2)))
            (extend (library (idle 1 1) Kind.ebit) 2 1 M))) i j
          = if i.1 = i.2 ∧ j.1 = j.2 then M (i.1, 0) (j.1, 0) else 0 := by
      intro M i j
      rcases i with ⟨x, z⟩; rcases j with ⟨x', z'⟩
      simp only [localMap]
      erw [g69_K_apply]
      simp only [extend, library, cbitChannel, entangled, localMap]
      simp only [g69_perm_conj, g69_sj, g69_cn_join, g69_split1, g69_split2, g69_join1, g69_join2]
      fin_cases x <;> fin_cases z <;> fin_cases x' <;> fin_cases z' <;>
        simp [Fin.sum_univ_succ, pureDensity, maximallyEntangledKet, finiteMaxEntangled]
      all_goals (repeat erw [g69_perm_conj])
      all_goals simp [g69_cn]
      all_goals (rw [g69_h2]; ring)
    exact funext fun _ => funext fun M => funext fun i => funext fun j => key M i j

theorem g69_backward : Exact (idle 1 1) (budget 0 1 0 0 0 0 0 1) (reverse (cobitChannel 2)) := by
  have s1 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.ebit 1 2
  have s2 := Sequential.localStep (L := library (idle 1 1)) (D := Unit)
    (fun _ => (fun M => M : Superop (Fin (2*1)) (Fin (1*2))))
    (conjSuperop (g69_perm g69_cn))
    (fun _ => g69_chan_id (ι := Fin 2)) (g69_chan_conj _ (g69_perm_iso _ g69_cn_inv))
  have s3 := Sequential.callStep (L := library (idle 1 1)) (D := Unit) Kind.cbitB 2 2
  have s4 := Sequential.localStep (L := library (idle 1 1)) (D := Unit)
    (fun _ => krausApply g69_K)
    (fun M => M : Superop (Fin (1*2)) (Fin 2))
    (fun _ => ⟨2, g69_K, g69_K_kraus, fun _ => rfl⟩) (g69_chan_id (ι := Fin 2))
  have s := Sequential.compose (Sequential.compose (Sequential.compose s1 s2) s3) s4
  refine ⟨_, ?_, g69_seq_eq s ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have key : ∀ (M : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) (i j : Fin 2 × Fin 2),
        localMap (krausApply g69_K) (fun M => M : Superop (Fin (1*2)) (Fin 2))
          (extend (library (idle 1 1) Kind.cbitB) 2 2
          (localMap (fun M => M : Superop (Fin (2*1)) (Fin (1*2))) (conjSuperop (g69_perm g69_cn))
            (extend (library (idle 1 1) Kind.ebit) 1 2 M))) i j
          = if i.2 = i.1 ∧ j.2 = j.1 then M (0, i.2) (0, j.2) else 0 := by
      intro M i j
      rcases i with ⟨z, x⟩; rcases j with ⟨z', x'⟩
      simp only [localMap]
      erw [g69_K_apply]
      simp only [extend, library, cbitChannel, reverse, entangled, localMap]
      simp only [g69_sj, g69_split1, g69_split2, g69_join1, g69_join2]
      fin_cases x <;> fin_cases z <;> fin_cases x' <;> fin_cases z' <;>
        simp [Fin.sum_univ_succ, pureDensity, maximallyEntangledKet, finiteMaxEntangled]
      all_goals (repeat erw [g69_perm_conj])
      all_goals simp [g69_cn]
      all_goals (rw [g69_h2]; ring)
    exact funext fun _ => funext fun M => funext fun i => funext fun j => key M i j


theorem solution :
    Exact (idle 1 1) (budget 0 1 0 0 0 0 1 0) (cobitChannel 2) ∧
    Exact (idle 1 1) (budget 0 1 0 0 0 0 0 1) (reverse (cobitChannel 2)) :=
  ⟨g69_forward, g69_backward⟩
