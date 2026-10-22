-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.cnot_oneway
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:24:42.696591+00:00
-- url     : https://prove2.me/submissions/f6b70171-328d-41de-8e52-2e02637e21ac

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq
def g67a_Ucn : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  QAlgorithms.cnot.submatrix
      (fun i : Fin 2 × Fin 2 => (decide (i.1 = 1), decide (i.2 = 1)))
      (fun i : Fin 2 × Fin 2 => (decide (i.1 = 1), decide (i.2 = 1)))

lemma g67a_ext_cnot (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (i j : Fin 2 × Fin 2) :
    extend (library cnotResource Kind.main) 1 1 M i j = conjSuperop g67a_Ucn M i j := by
  have h1 : ∀ (x : Fin (library cnotResource Kind.main).ai) (z : Fin 1),
      (joinRegisters x z : Fin ((library cnotResource Kind.main).ai*1)) = x := by
    intro x z; ext; simp [joinRegisters, finProdFinEquiv_apply_val, Fin.val_eq_zero]
  have h1' : ∀ (x : Fin (library cnotResource Kind.main).bi) (z : Fin 1),
      (joinRegisters x z : Fin ((library cnotResource Kind.main).bi*1)) = x := by
    intro x z; ext; simp [joinRegisters, finProdFinEquiv_apply_val, Fin.val_eq_zero]
  have h2 : ∀ (x : Fin ((library cnotResource Kind.main).ao*1)),
      (split (b := 1) x).1 = x := by
    intro x; ext; simp [split, finProdFinEquiv_symm_apply, Fin.coe_divNat]
  have h2' : ∀ (x : Fin ((library cnotResource Kind.main).bo*1)),
      (split (b := 1) x).1 = x := by
    intro x; ext; simp [split, finProdFinEquiv_symm_apply, Fin.coe_divNat]
  simp only [extend, h1, h1', h2, h2']
  rfl

lemma g67a_localMap_apply {a b c d : ℕ} (A : Superop (Fin a) (Fin c)) (B : Superop (Fin b) (Fin d)) (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (i j : Fin c × Fin d) :
  localMap A B M i j = B (Matrix.of fun x y => A (Matrix.of fun u v => M (u,x) (v,y)) i.1 j.1) i.2 j.2 := rfl
lemma g67a_localMap_conj {a b c d : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (B : Matrix (Fin d) (Fin b) ℂ) :
    localMap (conjSuperop A) (conjSuperop B) =
      conjSuperop (Matrix.of fun (i : Fin c × Fin d) (k : Fin a × Fin b) => A i.1 k.1 * B i.2 k.2) := by
  funext M i j
  rw [g67a_localMap_apply]
  simp only [conjSuperop, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, star_mul']
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.1, x.1, x.2.2.2, x.2.1), invFun := fun x => (x.2.1, x.2.2.2, x.1, x.2.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring

lemma g67a_conj_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix μ κ ℂ)
    (M : Matrix ι ι ℂ) : conjSuperop B (conjSuperop A M) = conjSuperop (B * A) M := by
  simp [conjSuperop, Matrix.mul_assoc, Matrix.conjTranspose_mul]

lemma g67a_isChannel_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (A : Matrix κ ι ℂ)
    (h : Aᴴ * A = 1) : IsChannel (conjSuperop A) :=
  ⟨1, fun _ => A, by simpa [IsKrausFamily] using h, fun ρ => by simp [krausApply, conjSuperop]⟩

def g67a_ket0 : Matrix (Fin 2) (Fin 1) ℂ := fun i _ => if i = 0 then 1 else 0

def g67a_Vf : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 1) ℂ := fun i k => if i.1 = k.1 ∧ i.2 = k.1 then 1 else 0

lemma g67a_fwd_mat : g67a_Ucn * (Matrix.of fun (i : Fin 2 × Fin 2) (k : Fin 2 × Fin 1) =>
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i.1 k.1 * g67a_ket0 i.2 k.2) = g67a_Vf := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [g67a_Ucn, g67a_Vf, g67a_ket0, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      QAlgorithms.cnot, Matrix.one_apply]

lemma g67a_fwd_map (M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (i j : Fin 2 × Fin 2) :
    (cobitChannel 2).map M i j = conjSuperop g67a_Vf M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [cobitChannel, conjSuperop, g67a_Vf, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g67a_fwd_all (M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (i j : Fin 2 × Fin 2) :
    (cobitChannel 2).map M i j = extend (library cnotResource Kind.main) 1 1
      (localMap (conjSuperop (1 : Matrix (Fin 2) (Fin 2) ℂ)) (conjSuperop g67a_ket0) M) i j := by
  have h1 := g67a_ext_cnot (localMap (conjSuperop (1 : Matrix (Fin 2) (Fin 2) ℂ)) (conjSuperop g67a_ket0) M) i j
  have h2 : conjSuperop g67a_Ucn (localMap (conjSuperop (1 : Matrix (Fin 2) (Fin 2) ℂ)) (conjSuperop g67a_ket0) M) i j
      = conjSuperop g67a_Vf M i j := by
    rw [g67a_localMap_conj, g67a_conj_comp, g67a_fwd_mat]
  exact (g67a_fwd_map M i j).trans (h1.trans h2).symm

lemma g67a_part1 : Exact cnotResource (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) := by
  refine ⟨fun k => 0 + oneCall Kind.main k, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have hA : IsChannel (conjSuperop (1 : Matrix (Fin 2) (Fin 2) ℂ)) := g67a_isChannel_conj _ (by simp)
    have hB : IsChannel (conjSuperop g67a_ket0) := g67a_isChannel_conj _ (by
      ext i j; fin_cases i; fin_cases j; simp [g67a_ket0, Matrix.mul_apply, Fin.sum_univ_two])
    have e : (fun _ : Unit => (cobitChannel 2).map) = fun _ =>
        extend (library cnotResource Kind.main) 1 1 ∘ localMap (conjSuperop (1 : Matrix (Fin 2) (Fin 2) ℂ)) (conjSuperop g67a_ket0) := by
      funext _ M; funext i j
      exact g67a_fwd_all M i j
    rw [e]
    exact Sequential.compose (Sequential.localStep (fun _ => _) _ (fun _ => hA) hB) (Sequential.callStep Kind.main 1 1)

def g67a_s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
lemma g67a_ss : g67a_s * g67a_s = 1/2 := by
  unfold g67a_s
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
lemma g67a_s4 : g67a_s ^ 4 = 1/4 := by
  have : g67a_s ^ 4 = (g67a_s * g67a_s) * (g67a_s * g67a_s) := by ring
  rw [this, g67a_ss]; norm_num
lemma g67a_s2 : g67a_s ^ 2 = 1/2 := by rw [sq, g67a_ss]
lemma g67a_star_s : star g67a_s = g67a_s := by
  unfold g67a_s; simp [Complex.conj_ofReal]

lemma g67a_conj_s : (starRingEnd ℂ) g67a_s = g67a_s := g67a_star_s

def g67a_Hd : Matrix (Fin 2) (Fin 2) ℂ := fun i k => if i = 1 ∧ k = 1 then -g67a_s else g67a_s
def g67a_plus : Matrix (Fin 2) (Fin 1) ℂ := fun _ _ => g67a_s
def g67a_Vr : Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 2) ℂ := fun i k => if i.1 = k.2 ∧ i.2 = k.2 then 1 else 0

lemma g67a_Hd_unitary : g67a_Hdᴴ * g67a_Hd = 1 := by
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [g67a_Hd, Matrix.mul_apply, Fin.sum_univ_two, g67a_star_s, g67a_conj_s, g67a_ss] <;> (try ring_nf) <;> (try simp [g67a_s2]) <;> (try norm_num)

lemma g67a_plus_iso : g67a_plusᴴ * g67a_plus = 1 := by
  ext i k; fin_cases i; fin_cases k
  simp [g67a_plus, Matrix.mul_apply, Fin.sum_univ_two, g67a_star_s, g67a_ss]

lemma g67a_rev_mat : (Matrix.of fun (i : Fin 2 × Fin 2) (k : Fin 2 × Fin 2) => g67a_Hd i.1 k.1 * g67a_Hd i.2 k.2) *
    (g67a_Ucn * (Matrix.of fun (i : Fin 2 × Fin 2) (k : Fin 1 × Fin 2) => g67a_plus i.1 k.1 * g67a_Hd i.2 k.2))
    = g67a_Vr := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [g67a_Ucn, g67a_Vr, g67a_Hd, g67a_plus, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      QAlgorithms.cnot] <;> ring_nf <;> simp [g67a_s4]

lemma g67a_rev_map (M : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) (i j : Fin 2 × Fin 2) :
    (reverse (cobitChannel 2)).map M i j = conjSuperop g67a_Vr M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [reverse, cobitChannel, conjSuperop, g67a_Vr, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g67a_rev_all (M : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) (i j : Fin 2 × Fin 2) :
    (reverse (cobitChannel 2)).map M i j = localMap (conjSuperop g67a_Hd) (conjSuperop g67a_Hd)
      (extend (library cnotResource Kind.main) 1 1
        (localMap (conjSuperop g67a_plus) (conjSuperop g67a_Hd) M)) i j := by
  have h1 : extend (library cnotResource Kind.main) 1 1 (localMap (conjSuperop g67a_plus) (conjSuperop g67a_Hd) M)
      = conjSuperop g67a_Ucn (localMap (conjSuperop g67a_plus) (conjSuperop g67a_Hd) M) :=
    funext fun i => funext fun j => g67a_ext_cnot _ i j
  have e := congrArg (fun Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ =>
    localMap (conjSuperop g67a_Hd) (conjSuperop g67a_Hd) Z i j) h1
  refine (g67a_rev_map M i j).trans (Eq.symm (e.trans ?_))
  rw [g67a_localMap_conj, g67a_localMap_conj, g67a_conj_comp, g67a_conj_comp, Matrix.mul_assoc, g67a_rev_mat]

lemma g67a_part2 : Exact cnotResource (budget 1 0 0 0 0 0 0 0) (reverse (cobitChannel 2)) := by
  refine ⟨fun k => (0 + oneCall Kind.main k) + 0, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have hA : IsChannel (conjSuperop g67a_plus) := g67a_isChannel_conj _ g67a_plus_iso
    have hB : IsChannel (conjSuperop g67a_Hd) := g67a_isChannel_conj _ g67a_Hd_unitary
    have e : (fun _ : Unit => (reverse (cobitChannel 2)).map) = fun _ =>
        localMap (conjSuperop g67a_Hd) (conjSuperop g67a_Hd) ∘
        (extend (library cnotResource Kind.main) 1 1 ∘ localMap (conjSuperop g67a_plus) (conjSuperop g67a_Hd)) := by
      funext _ M; funext i j
      exact g67a_rev_all M i j
    rw [e]
    exact Sequential.compose
      (Sequential.compose (Sequential.localStep (fun _ => _) _ (fun _ => hA) hB) (Sequential.callStep Kind.main 1 1))
      (Sequential.localStep (fun _ => _) _ (fun _ => hB) hB)

theorem solution :
    Exact cnotResource (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) ∧
    Exact cnotResource (budget 1 0 0 0 0 0 0 0) (reverse (cobitChannel 2)) :=
  ⟨g67a_part1, g67a_part2⟩

end
