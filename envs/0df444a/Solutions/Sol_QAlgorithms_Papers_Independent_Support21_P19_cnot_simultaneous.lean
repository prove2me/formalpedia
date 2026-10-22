-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.cnot_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:46:33.804815+00:00
-- url     : https://prove2.me/submissions/de22018d-67c7-42d9-9543-29523f0dced4

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq
def g67a_jeq (a b c d : ℕ) : (Fin a × Fin b) × (Fin c × Fin d) ≃ Fin (a*c) × Fin (b*d) :=
  (Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv)

@[simp] lemma g67a_jeq_apply {a b c d : ℕ} (x : Fin a × Fin b) (u : Fin c × Fin d) :
    g67a_jeq a b c d (x, u) = (joinRegisters x.1 u.1, joinRegisters x.2 u.2) := rfl

@[simp] lemma g67a_split_join {a b : ℕ} (x : Fin a) (y : Fin b) : split (joinRegisters x y) = (x, y) :=
  finProdFinEquiv.symm_apply_apply (x, y)

lemma g67a_sum_j {a b c d : ℕ} (f : Fin (a*c) × Fin (b*d) → ℂ) :
    ∑ k, f k = ∑ x : Fin a × Fin b, ∑ u : Fin c × Fin d, f (joinRegisters x.1 u.1, joinRegisters x.2 u.2) := by
  rw [← Fintype.sum_prod_type', ← (g67a_jeq a b c d).sum_comp]; rfl

lemma g67a_ext_j {a b c d : ℕ} {κ : Type*} {X Y : Matrix (Fin (a*c) × Fin (b*d)) κ ℂ}
    (h : ∀ (x : Fin a × Fin b) (u : Fin c × Fin d) k,
      X (joinRegisters x.1 u.1, joinRegisters x.2 u.2) k = Y (joinRegisters x.1 u.1, joinRegisters x.2 u.2) k) :
    X = Y := by
  ext i k
  obtain ⟨⟨x, u⟩, rfl⟩ := (g67a_jeq a b c d).surjective i
  exact h x u k

/-- Kronecker-type matrix in the join/split convention. -/
def g67a_kj {a b c d a' b' c' d' : ℕ} (A : Matrix (Fin a × Fin b) (Fin a' × Fin b') ℂ)
    (B : Matrix (Fin c × Fin d) (Fin c' × Fin d') ℂ) :
    Matrix (Fin (a*c) × Fin (b*d)) (Fin (a'*c') × Fin (b'*d')) ℂ :=
  fun i k => A ((split i.1).1, (split i.2).1) ((split k.1).1, (split k.2).1) *
    B ((split i.1).2, (split i.2).2) ((split k.1).2, (split k.2).2)

lemma g67a_extend_apply (R : Resource) (ma mb : ℕ) (M : Matrix (Fin (R.ai*ma) × Fin (R.bi*mb)) (Fin (R.ai*ma) × Fin (R.bi*mb)) ℂ) (i j : Fin (R.ao*ma) × Fin (R.bo*mb)) :
    extend R ma mb M i j = R.map (Matrix.of fun x y => M (joinRegisters x.1 (split i.1).2,joinRegisters x.2 (split i.2).2)
      (joinRegisters y.1 (split j.1).2,joinRegisters y.2 (split j.2).2))
    ((split i.1).1,(split i.2).1) ((split j.1).1,(split j.2).1) := rfl

lemma g67a_star_ind (p : Prop) [Decidable p] : star (if p then (1:ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma g67a_star_ite (p : Prop) [Decidable p] (x : ℂ) : star (if p then x else 0) = if p then star x else 0 := by
  split_ifs <;> simp

lemma g67a_extend_conj (R : Resource) (A : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (hR : R.map = conjSuperop A) (ma mb : ℕ) :
    extend R ma mb = conjSuperop (g67a_kj A (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  funext M i j
  rw [g67a_extend_apply]
  simp only [hR, conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [g67a_sum_j]
  simp only [g67a_sum_j (f := fun k => _ * star _), Finset.sum_mul]
  simp only [g67a_kj, g67a_split_join, Matrix.one_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
    star_mul', g67a_star_ind, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, g67a_star_ite, star_zero]

lemma g67a_tensor_conj (R S : Resource) (A : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (B : Matrix (Fin S.ao × Fin S.bo) (Fin S.ai × Fin S.bi) ℂ)
    (hR : R.map = conjSuperop A) (hS : S.map = conjSuperop B)
    (M : Matrix (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) ℂ)
    (i j : Fin (R.ao*S.ao) × Fin (R.bo*S.bo)) :
    (tensorResources R S).map M i j = conjSuperop (g67a_kj A B) M i j := by
  simp only [tensorResources, hR, hS, conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [g67a_sum_j]
  simp only [g67a_sum_j (f := fun k => _ * star _), Finset.sum_mul]
  simp only [g67a_kj, g67a_split_join, Matrix.single_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
    star_mul', g67a_star_ind, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, g67a_star_ite, star_zero]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2, t.1, t.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1),
      invFun := fun r => (r.2.2.2.2.1, r.2.2.2.2.2.1, r.1, r.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2, r.2.2.1, r.2.2.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring

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

/-! ## cnot_simultaneous -/

def g67a_phi : Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 1) ℂ := fun p _ => if p.1 = p.2 then g67a_s else 0

lemma g67a_ent_pt (M : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (i j : Fin 2 × Fin 2) :
    (entangled 2).map M i j = conjSuperop g67a_phi M i j := by
  simp [entangled, pureDensity, maximallyEntangledKet, finiteMaxEntangled, conjSuperop, g67a_phi,
    Matrix.mul_apply, g67a_s, Fintype.sum_prod_type]
  split_ifs <;> simp <;> ring

lemma g67a_ent_map : (library cnotResource Kind.ebit).map = conjSuperop g67a_phi :=
  funext fun M => funext fun i => funext fun j => g67a_ent_pt M i j

def g67a_A1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ :=
  fun i k => if split i = ((split k).1 + (split k).2, (split k).2) then 1 else 0
def g67a_B1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ :=
  fun i k => if i = k then (if (split k).1 = 1 ∧ (split k).2 = 1 then -1 else 1) else 0
def g67a_A3 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ :=
  fun i k => if (split i).1 = (split k).2 then
    g67a_Hd (split i).2 (split k).1 * (if (split k).2 = 1 ∧ (split i).2 = 1 then -1 else 1) else 0

def g67a_Ke : Matrix (Fin (2*2) × Fin (2*2)) (Fin (1*2) × Fin (1*2)) ℂ :=
  g67a_kj g67a_phi (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
def g67a_Kc : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*2) × Fin (2*2)) ℂ :=
  g67a_kj g67a_Ucn (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
def g67a_VT : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*1) × Fin (1*2)) ℂ := g67a_kj g67a_Vf g67a_Vr

lemma g67a_ext_jj {a b c d a' b' c' d' : ℕ}
    {X Y : Matrix (Fin (a*c) × Fin (b*d)) (Fin (a'*c') × Fin (b'*d')) ℂ}
    (h : ∀ (x : Fin a × Fin b) (u : Fin c × Fin d) (y : Fin a' × Fin b') (w : Fin c' × Fin d'),
      X (joinRegisters x.1 u.1, joinRegisters x.2 u.2) (joinRegisters y.1 w.1, joinRegisters y.2 w.2) =
      Y (joinRegisters x.1 u.1, joinRegisters x.2 u.2) (joinRegisters y.1 w.1, joinRegisters y.2 w.2)) :
    X = Y := by
  ext i k
  obtain ⟨⟨x, u⟩, rfl⟩ := (g67a_jeq a b c d).surjective i
  obtain ⟨⟨y, w⟩, rfl⟩ := (g67a_jeq a' b' c' d').surjective k
  exact h x u y w

@[simp] lemma g67a_join_inj {a b : ℕ} (x x' : Fin a) (y y' : Fin b) :
    joinRegisters x y = joinRegisters x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h; have := congrArg split h; simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] lemma g67a_split_join21 (p : Fin 2) (q : Fin 1) :
    split (a := 1) (b := 2) (joinRegisters (a := 2) (b := 1) p q) = (0, p) := by
  fin_cases p <;> fin_cases q <;> rfl

lemma g67a_sim_mat :
    (Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A3 i.1 k.1 * (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.2 k.2) *
    (g67a_Kc * ((Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * g67a_B1 i.2 k.2) * g67a_Ke)) = g67a_VT := by
  apply g67a_ext_jj (a' := 2) (c' := 1) (b' := 1) (d' := 2)
  intro x u y w
  simp only [Matrix.mul_apply, g67a_sum_j, Matrix.of_apply, g67a_Kc, g67a_Ke, g67a_VT, g67a_kj, g67a_split_join,
    g67a_A1, g67a_B1, g67a_A3]
  simp only [g67a_split_join, g67a_split_join21, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq, Fintype.sum_prod_type,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  obtain ⟨x1, x2⟩ := x; obtain ⟨u1, u2⟩ := u; obtain ⟨y1, y2⟩ := y; obtain ⟨w1, w2⟩ := w
  fin_cases x1 <;> fin_cases x2 <;> fin_cases u1 <;> fin_cases u2 <;> fin_cases y1 <;> fin_cases y2 <;>
    fin_cases w1 <;> fin_cases w2 <;>
    simp [Fin.sum_univ_two, g67a_Hd, g67a_Ucn, g67a_phi, QAlgorithms.cnot, g67a_Vf, g67a_Vr] <;>
    ring_nf <;> simp [g67a_s2]


lemma g67a_e1 (M : Matrix (Fin (1*2) × Fin (1*2)) (Fin (1*2) × Fin (1*2)) ℂ) :
    extend (library cnotResource Kind.ebit) 2 2 M = conjSuperop g67a_Ke M := by
  have h := g67a_extend_conj (library cnotResource Kind.ebit) g67a_phi g67a_ent_map 2 2
  exact congrFun h M

lemma g67a_hC (X : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*2) × Fin (2*2)) ℂ) :
      extend (library cnotResource Kind.main) 2 2 X = conjSuperop g67a_Kc X := by
  have h := g67a_extend_conj (library cnotResource Kind.main) g67a_Ucn rfl 2 2
  exact congrFun h X

lemma g67a_ext4 {X Y : Matrix (Fin (2*2)) (Fin (2*2)) ℂ}
    (h : ∀ p q r t : Fin 2, X (joinRegisters p q) (joinRegisters r t) = Y (joinRegisters p q) (joinRegisters r t)) :
    X = Y := by
  ext i k
  obtain ⟨⟨p, q⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨⟨r, t⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective k
  exact h p q r t

lemma g67a_sum4 (f : Fin (2*2) → ℂ) : ∑ k, f k = ∑ p : Fin 2, ∑ q : Fin 2, f (joinRegisters p q) := by
  rw [← Fintype.sum_prod_type', ← (finProdFinEquiv (m := 2) (n := 2)).sum_comp]; rfl

lemma g67a_unit4 (A : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)
    (h : ∀ p q r t : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2,
      star (A (joinRegisters a b) (joinRegisters p q)) * A (joinRegisters a b) (joinRegisters r t) =
        if p = r ∧ q = t then 1 else 0) : Aᴴ * A = 1 := by
  apply g67a_ext4
  intro p q r t
  rw [Matrix.mul_apply, g67a_sum4]
  simp only [Matrix.conjTranspose_apply]
  rw [h, Matrix.one_apply]
  simp only [g67a_join_inj]

lemma g67a_A1_unit : g67a_A1ᴴ * g67a_A1 = 1 := by
  apply g67a_unit4; intro p q r t
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases t <;>
    simp only [g67a_A1, Fin.sum_univ_two, g67a_join_inj, g67a_split_join] <;> simp

lemma g67a_B1_unit : g67a_B1ᴴ * g67a_B1 = 1 := by
  apply g67a_unit4; intro p q r t
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases t <;>
    simp only [g67a_B1, Fin.sum_univ_two, g67a_join_inj, g67a_split_join] <;> simp

lemma g67a_A3_unit : g67a_A3ᴴ * g67a_A3 = 1 := by
  apply g67a_unit4; intro p q r t
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases t <;>
    simp [g67a_A3, g67a_Hd, Fin.sum_univ_two, g67a_conj_s] <;> ring_nf <;> simp [g67a_s2] <;> norm_num

lemma g67a_sim_all (M : Matrix (Fin (2*1) × Fin (1*2)) (Fin (2*1) × Fin (1*2)) ℂ) (i j : Fin (2*2) × Fin (2*2)) :
    (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))).map M i j =
    localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ))
      (extend (library cnotResource Kind.main) 2 2
        (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1)
          (extend (library cnotResource Kind.ebit) 2 2 M))) i j := by
  have hR : (cobitChannel 2).map = conjSuperop g67a_Vf :=
    funext fun M => funext fun i => funext fun j => g67a_fwd_map M i j
  have hS : (reverse (cobitChannel 2)).map = conjSuperop g67a_Vr :=
    funext fun M => funext fun i => funext fun j => g67a_rev_map M i j
  have hT := g67a_tensor_conj (cobitChannel 2) (reverse (cobitChannel 2)) g67a_Vf g67a_Vr hR hS M i j
  have e1 : extend (library cnotResource Kind.ebit) 2 2 M = conjSuperop g67a_Ke M := g67a_e1 M
  have e2 : localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1) (extend (library cnotResource Kind.ebit) 2 2 M)
      = conjSuperop ((Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * g67a_B1 i.2 k.2) * g67a_Ke) M := by
    rw [e1, g67a_localMap_conj, g67a_conj_comp]
  have hC := g67a_hC
  have e3 : extend (library cnotResource Kind.main) 2 2
      (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1) (extend (library cnotResource Kind.ebit) 2 2 M))
      = conjSuperop (g67a_Kc * ((Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * g67a_B1 i.2 k.2) * g67a_Ke)) M := by
    exact (hC _).trans ((congrArg (conjSuperop g67a_Kc) e2).trans (g67a_conj_comp _ _ M))
  have e4 := congrArg (fun Z : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*2) × Fin (2*2)) ℂ =>
    localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) Z i j) e3
  refine hT.trans (Eq.symm (e4.trans ?_))
  rw [g67a_localMap_conj, g67a_conj_comp, g67a_sim_mat]
  rfl

lemma g67a_sim : Exact cnotResource (budget 1 1 0 0 0 0 0 0)
    (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))) := by
  refine ⟨fun k => ((oneCall Kind.ebit k + 0) + oneCall Kind.main k) + 0, ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have hA1 : IsChannel (conjSuperop g67a_A1) := g67a_isChannel_conj _ g67a_A1_unit
    have hB1 : IsChannel (conjSuperop g67a_B1) := g67a_isChannel_conj _ g67a_B1_unit
    have hA3 : IsChannel (conjSuperop g67a_A3) := g67a_isChannel_conj _ g67a_A3_unit
    have hI : IsChannel (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) := g67a_isChannel_conj _ (by simp)
    have e : (fun _ : Unit => (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))).map) = fun _ =>
        localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) ∘
        (extend (library cnotResource Kind.main) 2 2 ∘
          (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1) ∘ extend (library cnotResource Kind.ebit) 2 2)) := by
      funext _ M; funext i j
      exact g67a_sim_all M i j
    rw [e]
    exact Sequential.compose
      (Sequential.compose
        (Sequential.compose (Sequential.callStep Kind.ebit 2 2)
          (Sequential.localStep (fun _ => _) _ (fun _ => hA1) hB1))
        (Sequential.callStep Kind.main 2 2))
      (Sequential.localStep (fun _ => _) _ (fun _ => hA3) hI)

theorem solution :
    Exact cnotResource (budget 1 1 0 0 0 0 0 0) (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))) :=
  g67a_sim

end
