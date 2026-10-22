-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.coherent_cnot_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:07:46.321292+00:00
-- url     : https://prove2.me/submissions/123e51d1-1db7-4ab2-a494-7ed21cc39330

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

/-! ## coherent CNOT (Eisert-type) -/

lemma g67a_sum_join {a b : ℕ} (f : Fin (a*b) → ℂ) :
    ∑ k, f k = ∑ x : Fin a, ∑ y : Fin b, f (joinRegisters x y) := by
  rw [← Fintype.sum_prod_type', ← (finProdFinEquiv (m := a) (n := b)).sum_comp]; rfl

lemma g67a_ext_join {a b : ℕ} {κ : Type*} {X Y : Matrix (Fin (a*b)) κ ℂ}
    (h : ∀ (x : Fin a) (y : Fin b) k, X (joinRegisters x y) k = Y (joinRegisters x y) k) : X = Y := by
  ext i k
  obtain ⟨⟨x, y⟩, rfl⟩ := (finProdFinEquiv (m := a) (n := b)).surjective i
  exact h x y k

lemma g67a_ext_join' {a b : ℕ} {κ : Type*} {X Y : Matrix κ (Fin (a*b)) ℂ}
    (h : ∀ i (x : Fin a) (y : Fin b), X i (joinRegisters x y) = Y i (joinRegisters x y)) : X = Y := by
  ext i k
  obtain ⟨⟨x, y⟩, rfl⟩ := (finProdFinEquiv (m := a) (n := b)).surjective k
  exact h i x y

@[simp] lemma g67a_x14 (p q : Fin 2) :
    split (a := 1) (b := 2*2) (joinRegisters (a := 2) (b := 2) p q) = (0, joinRegisters p q) := by
  fin_cases p <;> fin_cases q <;> rfl
@[simp] lemma g67a_x22 (x : Fin (2*2)) :
    split (a := 2) (b := 2) (joinRegisters (a := 1) (b := 2*2) 0 x) = split x := by
  fin_cases x <;> rfl
@[simp] lemma g67a_x12 (p : Fin 2) (q : Fin (1*(1*1))) :
    split (a := 1) (b := 2) (joinRegisters (a := 2) (b := 1*(1*1)) p q) = (0, p) := by
  fin_cases p <;> fin_cases q <;> rfl

def g67a_B4 : Matrix (Fin (2*(2*2))) (Fin (2*(2*2))) ℂ := fun i k =>
  if (split i).2 = joinRegisters (split k).1 ((split (split k).2).2 + (split k).1 + (split (split k).2).1) then
    g67a_Hd (split i).1 ((split (split k).2).1 + (split k).1) else 0

def g67a_A6 : Matrix (Fin (2*(2*(2*1)))) (Fin (2*(2*2))) ℂ := fun i k =>
  if i = joinRegisters (split (split k).2).2 (joinRegisters (split (split k).2).1 (joinRegisters (split k).1 0)) then
    (if (split (split k).2).2 = 1 ∧ (split k).1 = 1 then -1 else 1) else 0

def g67a_B6 : Matrix (Fin (2*(2*(2*1)))) (Fin (2*(2*2))) ℂ := fun i k =>
  if i = joinRegisters (split (split k).2).2 (joinRegisters (split (split k).2).1 (joinRegisters (split k).1 0)) then
    1 else 0


lemma g67a_ext8 {X Y : Matrix (Fin (2*(2*2))) (Fin (2*(2*2))) ℂ}
    (h : ∀ p q t p' q' t' : Fin 2, X (joinRegisters p (joinRegisters q t)) (joinRegisters p' (joinRegisters q' t')) =
      Y (joinRegisters p (joinRegisters q t)) (joinRegisters p' (joinRegisters q' t'))) : X = Y := by
  ext i k
  obtain ⟨⟨p, y⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*2)).surjective i
  obtain ⟨⟨q, t⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective y
  obtain ⟨⟨p', y'⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*2)).surjective k
  obtain ⟨⟨q', t'⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective y'
  exact h p q t p' q' t'

lemma g67a_B4_unit : g67a_B4ᴴ * g67a_B4 = 1 := by
  apply g67a_ext8; intro p q t p' q' t'
  rw [Matrix.mul_apply]
  simp only [g67a_sum_join, Matrix.conjTranspose_apply, g67a_B4, g67a_split_join, g67a_join_inj, Matrix.one_apply]
  fin_cases p <;> fin_cases q <;> fin_cases t <;> fin_cases p' <;> fin_cases q' <;> fin_cases t' <;>
    simp [Fin.sum_univ_two, g67a_Hd, g67a_conj_s] <;> ring_nf <;> simp [g67a_s2] <;> norm_num

lemma g67a_A6_unit : g67a_A6ᴴ * g67a_A6 = 1 := by
  apply g67a_ext8; intro p q t p' q' t'
  rw [Matrix.mul_apply]
  simp only [g67a_sum_join, Matrix.conjTranspose_apply, g67a_A6, g67a_split_join, g67a_join_inj, Matrix.one_apply]
  fin_cases p <;> fin_cases q <;> fin_cases t <;> fin_cases p' <;> fin_cases q' <;> fin_cases t' <;>
    simp [Fin.sum_univ_two]

lemma g67a_B6_unit : g67a_B6ᴴ * g67a_B6 = 1 := by
  apply g67a_ext8; intro p q t p' q' t'
  rw [Matrix.mul_apply]
  simp only [g67a_sum_join, Matrix.conjTranspose_apply, g67a_B6, g67a_split_join, g67a_join_inj, Matrix.one_apply]
  fin_cases p <;> fin_cases q <;> fin_cases t <;> fin_cases p' <;> fin_cases q' <;> fin_cases t' <;>
    simp [Fin.sum_univ_two]

@[simp] lemma g67a_x0 (x : Fin 1) (p q : Fin 2) :
    joinRegisters (a := 1) (b := 2*2) x (joinRegisters (a := 2) (b := 2) p q) = joinRegisters p q := by
  fin_cases x <;> fin_cases p <;> fin_cases q <;> rfl

def g67a_one1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ := fun _ _ => 1

lemma g67a_idle_pt (M : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (i j : Fin 1 × Fin 1) :
    (idle 1 1).map M i j = conjSuperop g67a_one1 M i j := by
  rw [Subsingleton.elim i (0, 0), Subsingleton.elim j (0, 0)]
  simp [idle, conjSuperop, g67a_one1, Matrix.mul_apply, Fintype.sum_prod_type]

lemma g67a_idle_map : (idle 1 1).map = conjSuperop g67a_one1 :=
  funext fun M => funext fun i => funext fun j => g67a_idle_pt M i j

lemma g67a_join_surj {a b : ℕ} (x : Fin (a*b)) : ∃ p q, x = joinRegisters (a := a) (b := b) p q :=
  ⟨(split x).1, (split x).2, (finProdFinEquiv.apply_symm_apply x).symm⟩

lemma g67a_E1_map : (tensorResources (entangled 2) (idle 1 1)).map = conjSuperop (g67a_kj g67a_phi g67a_one1) :=
  funext fun M => funext fun i => funext fun j =>
    g67a_tensor_conj (entangled 2) (idle 1 1) g67a_phi g67a_one1 g67a_ent_map g67a_idle_map M i j

lemma g67a_E2_map : (resourceTensorCopies (entangled 2) 2).map =
    conjSuperop (g67a_kj g67a_phi (g67a_kj g67a_phi g67a_one1)) :=
  funext fun M => funext fun i => funext fun j =>
    g67a_tensor_conj (entangled 2) (tensorResources (entangled 2) (idle 1 1)) g67a_phi _ g67a_ent_map g67a_E1_map M i j

def g67a_VC : Matrix (Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) ℂ :=
  g67a_kj g67a_Ucn (g67a_kj g67a_phi (g67a_kj g67a_phi g67a_one1))

lemma g67a_T_pt (M : Matrix (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) ℂ)
    (i j : Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) :
    (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)).map M i j = conjSuperop g67a_VC M i j :=
  g67a_tensor_conj cnotResource (resourceTensorCopies (entangled 2) 2) g67a_Ucn _ rfl g67a_E2_map M i j

def g67a_K3 : Matrix (Fin (2*2) × Fin (2*(2*2))) (Fin (2*2) × Fin (1*(2*2))) ℂ :=
  g67a_kj g67a_Vf (1 : Matrix (Fin 2 × Fin (2*2)) (Fin 2 × Fin (2*2)) ℂ)
def g67a_K5 : Matrix (Fin (2*(2*2)) × Fin (2*(2*2))) (Fin (1*(2*2)) × Fin (2*(2*2))) ℂ :=
  g67a_kj g67a_Vr (1 : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*2) × Fin (2*2)) ℂ)

lemma g67a_ent_map' : (library (idle 1 1) Kind.ebit).map = conjSuperop g67a_phi := g67a_ent_map
lemma g67a_cobF_map : (library (idle 1 1) Kind.cobitF).map = conjSuperop g67a_Vf :=
  funext fun M => funext fun i => funext fun j => g67a_fwd_map M i j
lemma g67a_cobB_map : (library (idle 1 1) Kind.cobitB).map = conjSuperop g67a_Vr :=
  funext fun M => funext fun i => funext fun j => g67a_rev_map M i j

lemma g67a_c1 (M : Matrix (Fin (1*2) × Fin (1*2)) (Fin (1*2) × Fin (1*2)) ℂ) :
    extend (library (idle 1 1) Kind.ebit) 2 2 M = conjSuperop g67a_Ke M := by
  have h := g67a_extend_conj (library (idle 1 1) Kind.ebit) g67a_phi g67a_ent_map' 2 2
  exact congrFun h M
lemma g67a_c3 (X : Matrix (Fin (2*2) × Fin (1*(2*2))) (Fin (2*2) × Fin (1*(2*2))) ℂ) :
    extend (library (idle 1 1) Kind.cobitF) 2 (2*2) X = conjSuperop g67a_K3 X := by
  have h := g67a_extend_conj (library (idle 1 1) Kind.cobitF) g67a_Vf g67a_cobF_map 2 (2*2)
  exact congrFun h X
lemma g67a_c5 (X : Matrix (Fin (1*(2*2)) × Fin (2*(2*2))) (Fin (1*(2*2)) × Fin (2*(2*2))) ℂ) :
    extend (library (idle 1 1) Kind.cobitB) (2*2) (2*2) X = conjSuperop g67a_K5 X := by
  have h := g67a_extend_conj (library (idle 1 1) Kind.cobitB) g67a_Vr g67a_cobB_map (2*2) (2*2)
  exact congrFun h X

lemma g67a_ext_T {X Y : Matrix (Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) ℂ}
    (h : ∀ (a' f1 f2 b' g1 g2 a b : Fin 2) (z z' : Fin 1) (w w' : Fin (1*(1*1))),
      X (joinRegisters a' (joinRegisters f1 (joinRegisters f2 z)), joinRegisters b' (joinRegisters g1 (joinRegisters g2 z')))
        (joinRegisters a w, joinRegisters b w') =
      Y (joinRegisters a' (joinRegisters f1 (joinRegisters f2 z)), joinRegisters b' (joinRegisters g1 (joinRegisters g2 z')))
        (joinRegisters a w, joinRegisters b w')) : X = Y := by
  ext ⟨i1, i2⟩ ⟨k1, k2⟩
  obtain ⟨⟨a', y⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*(2*1))).surjective i1
  obtain ⟨⟨f1, y2⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*1)).surjective y
  obtain ⟨⟨f2, z⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 1)).surjective y2
  obtain ⟨⟨b', v⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*(2*1))).surjective i2
  obtain ⟨⟨g1, v2⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2*1)).surjective v
  obtain ⟨⟨g2, z'⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 1)).surjective v2
  obtain ⟨⟨a, w⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 1*(1*1))).surjective k1
  obtain ⟨⟨b, w'⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 1*(1*1))).surjective k2
  exact h a' f1 f2 b' g1 g2 a b z z' w w'


def g67a_S2 : Matrix (Fin (2*2) × Fin (2*2)) (Fin (1*2) × Fin (1*2)) ℂ := fun i k =>
  if (split i.1).2 = (split k.1).2 ∧ (split i.2).2 = (split k.2).2 ∧ (split i.1).1 = (split i.2).1 + (split k.1).2
  then g67a_s else 0
def g67a_S3 : Matrix (Fin (2*2) × Fin (2*(2*2))) (Fin (1*2) × Fin (1*2)) ℂ := fun i k =>
  if (split i.1).2 = (split k.1).2 ∧ (split (split i.2).2).2 = (split k.2).2 ∧ (split i.2).1 = (split i.1).1 ∧
    (split i.1).1 = (split (split i.2).2).1 + (split k.1).2
  then g67a_s else 0
def g67a_S4 : Matrix (Fin (2*2) × Fin (2*(2*2))) (Fin (1*2) × Fin (1*2)) ℂ := fun i k =>
  if (split i.1).2 = (split k.1).2 ∧ (split (split i.2).2).2 = (split k.2).2 + (split k.1).2 ∧
    (split (split i.2).2).1 = (split i.1).1
  then g67a_s * g67a_Hd (split i.2).1 (split k.1).2 else 0
def g67a_S5 : Matrix (Fin (2*(2*2)) × Fin (2*(2*2))) (Fin (1*2) × Fin (1*2)) ℂ := fun i k =>
  if (split i.1).1 = (split i.2).1 ∧ (split (split i.1).2).2 = (split k.1).2 ∧
    (split (split i.2).2).2 = (split k.2).2 + (split k.1).2 ∧ (split (split i.2).2).1 = (split (split i.1).2).1
  then g67a_s * g67a_Hd (split i.2).1 (split k.1).2 else 0
def g67a_VC' : Matrix (Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) (Fin (1*2) × Fin (1*2)) ℂ := g67a_VC

@[simp] lemma g67a_x21 (w : Fin 1) (p : Fin 2) :
    split (a := 2) (b := 1*(1*1)) (joinRegisters (a := 1) (b := 2) w p) = (p, 0) := by
  fin_cases p <;> fin_cases w <;> rfl

set_option maxHeartbeats 4000000 in
lemma g67a_L2 : (Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.2 k.2) * g67a_Ke = g67a_S2 := by
  apply g67a_ext_jj (a := 2) (c := 2) (b := 2) (d := 2) (a' := 1) (c' := 2) (b' := 1) (d' := 2)
  rintro ⟨x1, x2⟩ ⟨u1, u2⟩ ⟨y1, y2⟩ ⟨w1, w2⟩
  simp only [Matrix.mul_apply, g67a_sum_j, Fintype.sum_prod_type, g67a_sum_join, Matrix.of_apply, g67a_Ke, g67a_S2, g67a_kj,
    g67a_A1, g67a_split_join, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases u1 <;> fin_cases u2 <;> fin_cases y1 <;> fin_cases y2 <;>
    fin_cases w1 <;> fin_cases w2 <;> simp [Fin.sum_univ_two, g67a_phi]

set_option maxHeartbeats 4000000 in
lemma g67a_L3 : g67a_K3 * g67a_S2 = g67a_S3 := by
  apply g67a_ext_jj (a := 2) (c := 2) (b := 2) (d := 2*2) (a' := 1) (c' := 2) (b' := 1) (d' := 2)
  rintro ⟨x1, x2⟩ ⟨u1, u2⟩ ⟨y1, y2⟩ ⟨w1, w2⟩
  obtain ⟨p, q, rfl⟩ := g67a_join_surj (a := 2) (b := 2) u2
  simp only [Matrix.mul_apply, g67a_sum_j, Fintype.sum_prod_type, g67a_sum_join, Matrix.of_apply, g67a_K3, g67a_S2,
    g67a_S3, g67a_kj, g67a_split_join, g67a_x14, g67a_x22, g67a_x0, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases u1 <;> fin_cases p <;> fin_cases q <;> fin_cases y1 <;> fin_cases y2 <;>
    fin_cases w1 <;> fin_cases w2 <;> simp [Fin.sum_univ_two, g67a_Vf]

set_option maxHeartbeats 4000000 in
lemma g67a_L4 : (Matrix.of fun (i : Fin (2*2) × Fin (2*(2*2))) (k : Fin (2*2) × Fin (2*(2*2))) =>
      (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.1 k.1 * g67a_B4 i.2 k.2) * g67a_S3 = g67a_S4 := by
  apply g67a_ext_jj (a := 2) (c := 2) (b := 2) (d := 2*2) (a' := 1) (c' := 2) (b' := 1) (d' := 2)
  rintro ⟨x1, x2⟩ ⟨u1, u2⟩ ⟨y1, y2⟩ ⟨w1, w2⟩
  obtain ⟨p, q, rfl⟩ := g67a_join_surj (a := 2) (b := 2) u2
  simp only [Matrix.mul_apply, g67a_sum_j, Fintype.sum_prod_type, g67a_sum_join, Matrix.of_apply, g67a_B4, g67a_S3,
    g67a_S4, g67a_split_join, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases u1 <;> fin_cases p <;> fin_cases q <;> fin_cases y1 <;> fin_cases y2 <;>
    fin_cases w1 <;> fin_cases w2 <;> simp [Fin.sum_univ_two, g67a_Hd] <;> ring

set_option maxHeartbeats 4000000 in
lemma g67a_L5 : g67a_K5 * g67a_S4 = g67a_S5 := by
  apply g67a_ext_jj (a := 2) (c := 2*2) (b := 2) (d := 2*2) (a' := 1) (c' := 2) (b' := 1) (d' := 2)
  rintro ⟨x1, x2⟩ ⟨u1, u2⟩ ⟨y1, y2⟩ ⟨w1, w2⟩
  obtain ⟨p, q, rfl⟩ := g67a_join_surj (a := 2) (b := 2) u1
  obtain ⟨p', q', rfl⟩ := g67a_join_surj (a := 2) (b := 2) u2
  simp only [Matrix.mul_apply, g67a_sum_j, Fintype.sum_prod_type, g67a_sum_join, Matrix.of_apply, g67a_K5, g67a_S4,
    g67a_S5, g67a_kj, g67a_split_join, g67a_x14, g67a_x22, g67a_x0, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases p <;> fin_cases q <;> fin_cases p' <;> fin_cases q' <;>
    fin_cases y1 <;> fin_cases y2 <;> fin_cases w1 <;> fin_cases w2 <;> simp [Fin.sum_univ_two, g67a_Vr]

set_option maxHeartbeats 4000000 in
lemma g67a_L6 : (Matrix.of fun (i : Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) (k : Fin (2*(2*2)) × Fin (2*(2*2))) =>
      g67a_A6 i.1 k.1 * g67a_B6 i.2 k.2) * g67a_S5 = g67a_VC' := by
  apply g67a_ext_jj (a := 2) (c := 2*(2*1)) (b := 2) (d := 2*(2*1)) (a' := 1) (c' := 2) (b' := 1) (d' := 2)
  rintro ⟨x1, x2⟩ ⟨u1, u2⟩ ⟨y1, y2⟩ ⟨w1, w2⟩
  obtain ⟨p, r, rfl⟩ := g67a_join_surj (a := 2) (b := 2*1) u1
  obtain ⟨q, z, rfl⟩ := g67a_join_surj (a := 2) (b := 1) r
  obtain ⟨p', r', rfl⟩ := g67a_join_surj (a := 2) (b := 2*1) u2
  obtain ⟨q', z', rfl⟩ := g67a_join_surj (a := 2) (b := 1) r'
  simp only [Matrix.mul_apply, g67a_sum_j, Fintype.sum_prod_type, g67a_sum_join, Matrix.of_apply, g67a_A6, g67a_B6,
    g67a_S5, g67a_VC', g67a_VC, g67a_kj, g67a_split_join, g67a_x21, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases p <;> fin_cases q <;> fin_cases p' <;> fin_cases q' <;>
    fin_cases y1 <;> fin_cases y2 <;> fin_cases w1 <;> fin_cases w2 <;> fin_cases z <;> fin_cases z' <;>
    simp [Fin.sum_univ_two, g67a_Hd, g67a_Ucn, QAlgorithms.cnot, g67a_phi, g67a_one1] <;> (try ring_nf) <;> (try simp [g67a_s2])

lemma g67a_coh_mat :
    (Matrix.of fun (i : Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) (k : Fin (2*(2*2)) × Fin (2*(2*2))) =>
      g67a_A6 i.1 k.1 * g67a_B6 i.2 k.2) *
    (g67a_K5 * ((Matrix.of fun (i : Fin (2*2) × Fin (2*(2*2))) (k : Fin (2*2) × Fin (2*(2*2))) =>
      (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.1 k.1 * g67a_B4 i.2 k.2) *
    (g67a_K3 * ((Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.2 k.2) * g67a_Ke)))) = g67a_VC' := by
  rw [g67a_L2, g67a_L3, g67a_L4, g67a_L5, g67a_L6]

lemma g67a_coh_all (M : Matrix (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) (Fin (2*(1*(1*1))) × Fin (2*(1*(1*1)))) ℂ)
    (i j : Fin (2*(2*(2*1))) × Fin (2*(2*(2*1)))) :
    (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)).map M i j =
    localMap (conjSuperop g67a_A6) (conjSuperop g67a_B6)
      (extend (library (idle 1 1) Kind.cobitB) (2*2) (2*2)
        (localMap (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) (conjSuperop g67a_B4)
          (extend (library (idle 1 1) Kind.cobitF) 2 (2*2)
            (localMap (conjSuperop g67a_A1) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ))
              (extend (library (idle 1 1) Kind.ebit) 2 2 M))))) i j := by
  have f1 : extend (library (idle 1 1) Kind.ebit) 2 2 M = conjSuperop g67a_Ke M := g67a_c1 M
  have f2 : localMap (conjSuperop g67a_A1) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ))
      (extend (library (idle 1 1) Kind.ebit) 2 2 M) =
      conjSuperop ((Matrix.of fun (i : Fin (2*2) × Fin (2*2)) (k : Fin (2*2) × Fin (2*2)) =>
      g67a_A1 i.1 k.1 * (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ) i.2 k.2) * g67a_Ke) M := by
    rw [f1, g67a_localMap_conj, g67a_conj_comp]
  have f3 := (g67a_c3 _).trans ((congrArg (conjSuperop g67a_K3) f2).trans (g67a_conj_comp _ _ M))
  have f4 := (congrArg (localMap (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) (conjSuperop g67a_B4)) f3).trans
    (by rw [g67a_localMap_conj, g67a_conj_comp])
  have f5 := (g67a_c5 _).trans ((congrArg (conjSuperop g67a_K5) f4).trans (g67a_conj_comp _ _ M))
  have f6 := congrArg (fun Z : Matrix (Fin (2*(2*2)) × Fin (2*(2*2))) (Fin (2*(2*2)) × Fin (2*(2*2))) ℂ =>
    localMap (conjSuperop g67a_A6) (conjSuperop g67a_B6) Z i j) f5
  refine (g67a_T_pt M i j).trans (Eq.symm (f6.trans ?_))
  rw [g67a_localMap_conj, g67a_conj_comp, g67a_coh_mat]
  rfl

lemma g67a_coh : Exact (idle 1 1) (budget 0 1 0 0 1 1 0 0)
    (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)) := by
  refine ⟨fun k => (((((oneCall Kind.ebit k + 0) + oneCall Kind.cobitF k) + 0) + oneCall Kind.cobitB k) + 0),
    ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have hA1 : IsChannel (conjSuperop g67a_A1) := g67a_isChannel_conj _ g67a_A1_unit
    have hB4 : IsChannel (conjSuperop g67a_B4) := g67a_isChannel_conj _ g67a_B4_unit
    have hA6 : IsChannel (conjSuperop g67a_A6) := g67a_isChannel_conj _ g67a_A6_unit
    have hB6 : IsChannel (conjSuperop g67a_B6) := g67a_isChannel_conj _ g67a_B6_unit
    have hI : IsChannel (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) := g67a_isChannel_conj _ (by simp)
    have e : (fun _ : Unit => (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)).map) = fun _ =>
        localMap (conjSuperop g67a_A6) (conjSuperop g67a_B6) ∘
        (extend (library (idle 1 1) Kind.cobitB) (2*2) (2*2) ∘
        (localMap (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) (conjSuperop g67a_B4) ∘
        (extend (library (idle 1 1) Kind.cobitF) 2 (2*2) ∘
        (localMap (conjSuperop g67a_A1) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) ∘
          extend (library (idle 1 1) Kind.ebit) 2 2)))) := by
      funext _ M; funext i j
      exact g67a_coh_all M i j
    rw [e]
    exact Sequential.compose (Sequential.compose (Sequential.compose (Sequential.compose (Sequential.compose
      (Sequential.callStep Kind.ebit 2 2)
      (Sequential.localStep (fun _ => _) _ (fun _ => hA1) hI))
      (Sequential.callStep Kind.cobitF 2 (2*2)))
      (Sequential.localStep (fun _ => _) _ (fun _ => hI) hB4))
      (Sequential.callStep Kind.cobitB (2*2) (2*2)))
      (Sequential.localStep (fun _ => _) _ (fun _ => hA6) hB6)

/-! ## second conjunct, k = 1 -/

@[simp] lemma g67a_y21 (p : Fin 2) (q : Fin 1) :
    split (a := 2*1) (b := 1*1) (joinRegisters (a := 2) (b := 1) p q) = (joinRegisters p q, 0) := by
  fin_cases p <;> fin_cases q <;> rfl
@[simp] lemma g67a_y12 (q : Fin 1) (p : Fin 2) :
    split (a := 1*2) (b := 1*1) (joinRegisters (a := 1) (b := 2) q p) = (joinRegisters q p, 0) := by
  fin_cases p <;> fin_cases q <;> rfl

@[simp] lemma g67a_s21 (x : Fin (2*1)) : (split (a := 2) (b := 1) x).1 = x := by fin_cases x <;> rfl
@[simp] lemma g67a_s12 (x : Fin (1*2)) : (split (a := 1) (b := 2) x).2 = x := by fin_cases x <;> rfl

lemma g67a_simT_map : (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))).map = conjSuperop g67a_VT :=
  funext fun M => funext fun i => funext fun j =>
    g67a_tensor_conj (cobitChannel 2) (reverse (cobitChannel 2)) g67a_Vf g67a_Vr
      (funext fun M => funext fun i => funext fun j => g67a_fwd_map M i j)
      (funext fun M => funext fun i => funext fun j => g67a_rev_map M i j) M i j

def g67a_VTT : Matrix (Fin ((2*2)*(2*1)) × Fin ((2*2)*(2*1))) (Fin ((2*1)*(1*1)) × Fin ((1*2)*(1*1))) ℂ :=
  g67a_kj g67a_VT (g67a_kj g67a_phi g67a_one1)

lemma g67a_TT_pt (M : Matrix (Fin ((2*1)*(1*1)) × Fin ((1*2)*(1*1))) (Fin ((2*1)*(1*1)) × Fin ((1*2)*(1*1))) ℂ)
    (i j : Fin ((2*2)*(2*1)) × Fin ((2*2)*(2*1))) :
    (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2)))
      (resourceTensorCopies (entangled 2) 1)).map M i j = conjSuperop g67a_VTT M i j :=
  g67a_tensor_conj (tensorResources (cobitChannel 2) (reverse (cobitChannel 2)))
    (resourceTensorCopies (entangled 2) 1) g67a_VT _ g67a_simT_map g67a_E1_map M i j

def g67a_KE2 : Matrix (Fin (2*(2*2)) × Fin (2*(2*2))) (Fin (1*(2*2)) × Fin (1*(2*2))) ℂ :=
  g67a_kj g67a_phi (1 : Matrix (Fin (2*2) × Fin (2*2)) (Fin (2*2) × Fin (2*2)) ℂ)

lemma g67a_c7 (X : Matrix (Fin (1*(2*2)) × Fin (1*(2*2))) (Fin (1*(2*2)) × Fin (1*(2*2))) ℂ) :
    extend (library cnotResource Kind.ebit) (2*2) (2*2) X = conjSuperop g67a_KE2 X := by
  have h := g67a_extend_conj (library cnotResource Kind.ebit) g67a_phi g67a_ent_map (2*2) (2*2)
  exact congrFun h X

def g67a_P : Matrix (Fin ((2*2)*(2*1))) (Fin (2*(2*2))) ℂ := fun i k =>
  if i = joinRegisters (split k).2 (joinRegisters (split k).1 0) then 1 else 0

lemma g67a_P_unit : g67a_Pᴴ * g67a_P = 1 := by
  apply g67a_ext8; intro p q t p' q' t'
  rw [Matrix.mul_apply]
  simp only [g67a_sum_join, Matrix.conjTranspose_apply, g67a_P, g67a_split_join, g67a_join_inj, Matrix.one_apply]
  fin_cases p <;> fin_cases q <;> fin_cases t <;> fin_cases p' <;> fin_cases q' <;> fin_cases t' <;>
    simp [Fin.sum_univ_two]

lemma g67a_ext_TT {X Y : Matrix (Fin ((2*2)*(2*1)) × Fin ((2*2)*(2*1))) (Fin (2*1) × Fin (1*2)) ℂ}
    (h : ∀ (p q e p' q' e' a b : Fin 2) (z z' w w' : Fin 1),
      X (joinRegisters (joinRegisters p q) (joinRegisters e z), joinRegisters (joinRegisters p' q') (joinRegisters e' z'))
        (joinRegisters a w, joinRegisters w' b) =
      Y (joinRegisters (joinRegisters p q) (joinRegisters e z), joinRegisters (joinRegisters p' q') (joinRegisters e' z'))
        (joinRegisters a w, joinRegisters w' b)) : X = Y := by
  ext ⟨i1, i2⟩ ⟨k1, k2⟩
  obtain ⟨x, y, rfl⟩ := g67a_join_surj (a := 2*2) (b := 2*1) i1
  obtain ⟨p, q, rfl⟩ := g67a_join_surj (a := 2) (b := 2) x
  obtain ⟨e, z, rfl⟩ := g67a_join_surj (a := 2) (b := 1) y
  obtain ⟨x', y', rfl⟩ := g67a_join_surj (a := 2*2) (b := 2*1) i2
  obtain ⟨p', q', rfl⟩ := g67a_join_surj (a := 2) (b := 2) x'
  obtain ⟨e', z', rfl⟩ := g67a_join_surj (a := 2) (b := 1) y'
  obtain ⟨a, w, rfl⟩ := g67a_join_surj (a := 2) (b := 1) k1
  obtain ⟨w', b, rfl⟩ := g67a_join_surj (a := 1) (b := 2) k2
  exact h p q e p' q' e' a b z z' w w'

set_option maxHeartbeats 4000000 in
lemma g67a_k1_mat :
    (Matrix.of fun (i : Fin ((2*2)*(2*1)) × Fin ((2*2)*(2*1))) (k : Fin (2*(2*2)) × Fin (2*(2*2))) =>
      g67a_P i.1 k.1 * g67a_P i.2 k.2) * (g67a_KE2 * g67a_VT) = g67a_VTT := by
  apply g67a_ext_TT
  intro p q e p' q' e' a b z z' w w'
  simp only [Matrix.mul_apply, g67a_sum_j, Matrix.of_apply, Fintype.sum_prod_type, g67a_sum_join]
  simp only [g67a_KE2, g67a_VT, g67a_VTT, g67a_kj, g67a_P, g67a_split_join, g67a_x0, g67a_x14, g67a_x22,
    g67a_y21, g67a_y12, g67a_join_inj, Matrix.one_apply, Prod.mk.injEq,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel]
  fin_cases p <;> fin_cases q <;> fin_cases e <;> fin_cases p' <;> fin_cases q' <;> fin_cases e' <;>
    fin_cases a <;> fin_cases b <;> fin_cases z <;> fin_cases z' <;> fin_cases w <;> fin_cases w' <;>
    simp [Fin.sum_univ_two, g67a_phi, g67a_Vf, g67a_Vr, g67a_one1, g67a_s21, g67a_s12]

lemma g67a_k1_all (M : Matrix (Fin ((2*1)*(1*1)) × Fin ((1*2)*(1*1))) (Fin ((2*1)*(1*1)) × Fin ((1*2)*(1*1))) ℂ)
    (i j : Fin ((2*2)*(2*1)) × Fin ((2*2)*(2*1))) :
    (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2)))
      (resourceTensorCopies (entangled 2) 1)).map M i j =
    localMap (conjSuperop g67a_P) (conjSuperop g67a_P)
      (extend (library cnotResource Kind.ebit) (2*2) (2*2)
        (localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ))
          (extend (library cnotResource Kind.main) 2 2
            (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1)
              (extend (library cnotResource Kind.ebit) 2 2 M))))) i j := by
  have s : localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ))
          (extend (library cnotResource Kind.main) 2 2
            (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1)
              (extend (library cnotResource Kind.ebit) 2 2 M))) = conjSuperop g67a_VT M :=
    funext fun i => funext fun j => (g67a_sim_all M i j).symm.trans (congrFun (congrFun (congrFun g67a_simT_map M) i) j)
  have f7 := (g67a_c7 _).trans ((congrArg (conjSuperop g67a_KE2) s).trans (g67a_conj_comp _ _ M))
  have f8 := congrArg (fun Z : Matrix (Fin (2*(2*2)) × Fin (2*(2*2))) (Fin (2*(2*2)) × Fin (2*(2*2))) ℂ =>
    localMap (conjSuperop g67a_P) (conjSuperop g67a_P) Z i j) f7
  refine (g67a_TT_pt M i j).trans (Eq.symm (f8.trans ?_))
  rw [g67a_localMap_conj, g67a_conj_comp, g67a_k1_mat]

lemma g67a_k1 : Exact cnotResource (budget 1 (1+1) 0 0 0 0 0 0)
    (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2)))
      (resourceTensorCopies (entangled 2) 1)) := by
  refine ⟨fun k => (((((oneCall Kind.ebit k + 0) + oneCall Kind.main k) + 0) + oneCall Kind.ebit k) + 0), ?_, ?_⟩
  · intro k; cases k <;> simp [oneCall, budget]
  · have hA1 : IsChannel (conjSuperop g67a_A1) := g67a_isChannel_conj _ g67a_A1_unit
    have hB1 : IsChannel (conjSuperop g67a_B1) := g67a_isChannel_conj _ g67a_B1_unit
    have hA3 : IsChannel (conjSuperop g67a_A3) := g67a_isChannel_conj _ g67a_A3_unit
    have hP : IsChannel (conjSuperop g67a_P) := g67a_isChannel_conj _ g67a_P_unit
    have hI : IsChannel (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) := g67a_isChannel_conj _ (by simp)
    have e : (fun _ : Unit => (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2)))
      (resourceTensorCopies (entangled 2) 1)).map) = fun _ =>
        localMap (conjSuperop g67a_P) (conjSuperop g67a_P) ∘
        (extend (library cnotResource Kind.ebit) (2*2) (2*2) ∘
        (localMap (conjSuperop g67a_A3) (conjSuperop (1 : Matrix (Fin (2*2)) (Fin (2*2)) ℂ)) ∘
        (extend (library cnotResource Kind.main) 2 2 ∘
          (localMap (conjSuperop g67a_A1) (conjSuperop g67a_B1) ∘ extend (library cnotResource Kind.ebit) 2 2)))) := by
      funext _ M; funext i j
      exact g67a_k1_all M i j
    rw [e]
    exact Sequential.compose (Sequential.compose
      (Sequential.compose
        (Sequential.compose
          (Sequential.compose (Sequential.callStep Kind.ebit 2 2)
            (Sequential.localStep (fun _ => _) _ (fun _ => hA1) hB1))
          (Sequential.callStep Kind.main 2 2))
        (Sequential.localStep (fun _ => _) _ (fun _ => hA3) hI))
      (Sequential.callStep Kind.ebit (2*2) (2*2)))
      (Sequential.localStep (fun _ => _) _ (fun _ => hP) hP)

theorem solution :
    Exact (idle 1 1) (budget 0 1 0 0 1 1 0 0) (tensorResources cnotResource (resourceTensorCopies (entangled 2) 2)) ∧
    ∃ k : ℕ,
      Exact (idle 1 1) (budget 0 k 0 0 1 1 0 0) (tensorResources cnotResource (resourceTensorCopies (entangled 2) (k+1))) ∧
      Exact cnotResource (budget 1 (k+1) 0 0 0 0 0 0)
        (tensorResources (tensorResources (cobitChannel 2) (reverse (cobitChannel 2))) (resourceTensorCopies (entangled 2) k)) :=
  ⟨g67a_coh, 1, g67a_coh, g67a_k1⟩

end
