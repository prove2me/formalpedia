-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T07:31:14.491328+00:00
-- url     : https://prove2.me/submissions/0e56fdfe-dc5c-490e-84f6-af2ee351b92c

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2
import Definitions.Def_OptimalTraceDistance_Estimation_HoeffdingGen
import Theorems.Thm_OptimalTraceDistance_Estimation_variance_le_effective_generic
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_1

open scoped BigOperators Matrix Classical ComplexOrder
noncomputable section

namespace OTDNorm
open Matrix OptimalTraceDistance.Estimation

lemma kron_mul {ι : Type*} [Fintype ι] {r : ℕ} (A B : Fin r → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun j => A j * B j) =
      OptimalSpectrum.Entangled.kronFamily A * OptimalSpectrum.Entangled.kronFamily B := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, mul_apply, Matrix.of_apply]
  have := Fintype.prod_sum (fun (j : Fin r) (c : ι) => A j (x j) c * B j c (y j))
  rw [this]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]


lemma path_prod {ι : Type*} [Fintype ι] [DecidableEq ι] : ∀ (k : ℕ) (B : Fin k → Matrix ι ι ℂ) (a b : ι),
    (List.ofFn B).prod a b = ∑ u : Fin (k+1) → ι,
      (if u 0 = a ∧ u (Fin.last k) = b then (1:ℂ) else 0) * ∏ i : Fin k, B i (u i.castSucc) (u i.succ)
  | 0, B, a, b => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    have h0 : ∀ c : ι, ((Equiv.funUnique (Fin 1) ι).symm c) 0 = c := fun c => rfl
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    simp only [hl, h0]
    rw [Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h]; symm
      exact Finset.sum_eq_zero (fun c _ => if_neg (fun hc => h (hc.1.symm.trans hc.2)))
  | k+1, B, a, b => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [path_prod k]
    rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.prod_univ_succ, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.cons_one, Fin.castSucc_succ, Fin.cons_succ, ← Fin.succ_last]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_eq_single (u 0)]
      · by_cases hb : u (Fin.last k) = b <;> simp [hb]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero (fun u _ => ?_); simp [hc]
    · simp

lemma cyc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (B : Fin (m+1) → Matrix ι ι ℂ) :
    ∑ w : Fin (m+1) → ι, ∏ i : Fin (m+1), B i (w i) (w ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) =
      ((List.ofFn B).prod).trace := by
  simp only [Matrix.trace, Matrix.diag, path_prod]
  rw [Finset.sum_comm]
  have h1 : ∀ u : Fin (m+2) → ι, ∑ a, (if u 0 = a ∧ u (Fin.last (m+1)) = a then (1:ℂ) else 0) *
      ∏ i : Fin (m+1), B i (u i.castSucc) (u i.succ) =
      (if u 0 = u (Fin.last (m+1)) then (1:ℂ) else 0) * ∏ i : Fin (m+1), B i (u i.castSucc) (u i.succ) := by
    intro u
    rw [Finset.sum_eq_single (u 0)]
    · by_cases h : u 0 = u (Fin.last (m+1))
      · simp [h]
      · simp [h, Ne.symm h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  simp only [h1]
  conv_rhs => rw [← (Fin.snocEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, Fin.snoc_castSucc]
  have h0 : (Fin.snoc w (w 0) : Fin (m+2) → ι) 0 = w 0 := by
    rw [show (0 : Fin (m+2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
  rw [Finset.sum_eq_single (w 0)]
  · rw [h0, if_pos rfl, one_mul]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    by_cases hi : i.val + 1 < m + 1
    · have : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩ := by ext; simp
      rw [this, Fin.snoc_castSucc]; congr 1; ext; simp [Nat.mod_eq_of_lt hi]
    · have hi' : i.val = m := by omega
      have : i.succ = Fin.last (m+1) := by ext; simp [hi']
      rw [this, Fin.snoc_last]; congr 1; ext; simp [hi']
  · intro c _ hc
    have : (Fin.snoc w c : Fin (m+2) → ι) 0 = w 0 := by
      rw [show (0 : Fin (m+2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    rw [this, if_neg (Ne.symm hc), zero_mul]
  · simp


lemma trace_shift {d : ℕ} (m : ℕ) (B : Fin (m+1) → Mat d) :
    (leftShift d (m+1) * tensor (m+1) B).trace = ((List.ofFn B).prod).trace := by
  rw [← cyc_trace]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, leftShift, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have : ∀ y : Fin (m+1) → Fin d, (∀ i : Fin (m+1), y i = u ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) ↔
      (fun i : Fin (m+1) => u ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) = y := by
    intro y; constructor
    · intro h; funext i; exact (h i).symm
    · rintro rfl i; rfl
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]


lemma tr2 {κ : Type*} [Fintype κ] (M N : Matrix κ κ ℂ) :
    (M * N).trace = ∑ x, ∑ y, M x y * N y x := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma sum_split {d k : ℕ} (f : (Fin k → Bool × Fin d) → ℂ) :
    ∑ x, f x = ∑ b : Fin k → Bool, ∑ z : Fin k → Fin d, f (fun i => (b i, z i)) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  rfl


/-- labelled block-diagonal operator built from a pair `(P,N)`: blocks `(P+N)/2`, `(P-N)/2`. -/
def Xl {d : ℕ} (P N : Mat d) : Matrix (Bool × Fin d) (Bool × Fin d) ℂ :=
  fun x y => if x.1 = y.1 then (2:ℂ)⁻¹ * (if x.1 then (P - N) else (P + N)) x.2 y.2 else 0

/-- cyclic word kernel with known matrices `B` and variable labels `t`. -/
def CK {d k : ℕ} (B : Fin k → Mat d) (t : Fin k → Bool) :
    Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ :=
  fun x y => if (fun i => (x i).1) = (fun i => (y i).1) then
    (∏ i, if t i && (x i).1 then (-1 : ℂ) else 1) *
      (leftShift d k * tensor k B) (fun i => (x i).2) (fun i => (y i).2) else 0

lemma Xl_labelled {d : ℕ} (ρ σ : Mat d) : Xl (plus ρ σ) (minus ρ σ) = labelledState ρ σ := by
  ext x y
  simp only [Xl, labelledState, plus, minus]
  by_cases h : x.1 = y.1
  · rw [if_pos h, if_pos h]
    by_cases hx : x.1
    · simp only [hx, if_true, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
    · simp only [hx, Bool.false_eq_true, if_false, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, smul_eq_mul]; ring
  · rw [if_neg h, if_neg h]

lemma label_sum_gen {d k : ℕ} (P N B : Fin k → Mat d) (t : Fin k → Bool) :
    (tensor k (fun i => Xl (P i) (N i)) * CK B t).trace =
      (tensor k (fun i => if t i then N i else P i) * (leftShift d k * tensor k B)).trace := by
  set V := leftShift d k * tensor k B with hV
  rw [tr2, tr2]
  simp only [CK]
  rw [sum_split]
  simp only [sum_split (fun y => _ * _)]
  have hP : ∀ (b b' : Fin k → Bool) (z z' : Fin k → Fin d),
      tensor k (fun i => Xl (P i) (N i)) (fun i => (b i, z i)) (fun i => (b' i, z' i)) =
        ∏ i, Xl (P i) (N i) (b i, z i) (b' i, z' i) := by
    intro b b' z z'; rfl
  simp only [hP]
  have hkill : ∀ (b : Fin k → Bool) (z : Fin k → Fin d),
      ∑ b' : Fin k → Bool, ∑ z' : Fin k → Fin d, (∏ i, Xl (P i) (N i) (b i, z i) (b' i, z' i)) *
        (if (fun i => b' i) = (fun i => b i) then
          (∏ i, if t i && b' i then (-1 : ℂ) else 1) * V z' z else 0) =
      ∑ z' : Fin k → Fin d, (∏ i, (if t i && b i then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if b i then (P i - N i) else (P i + N i)) (z i) (z' i))) * V z' z := by
    intro b z
    rw [Finset.sum_eq_single b]
    · refine Finset.sum_congr rfl (fun z' _ => ?_)
      simp only [if_true, Xl, Finset.prod_mul_distrib]
      ring
    · intro b' _ hb'
      refine Finset.sum_eq_zero (fun z' _ => ?_)
      rw [if_neg (fun h => hb' h), mul_zero]
    · simp
  simp only [← hV]
  simp only [hkill]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z' _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun i c => (if t i && c then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if c then (P i - N i) else (P i + N i)) (z i) (z' i)))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Fintype.sum_bool, Bool.and_true, Bool.and_false, if_true, Bool.false_eq_true, if_false]
  by_cases hti : t i
  · rw [if_pos hti, if_pos hti]
    simp only [Matrix.sub_apply, Matrix.add_apply]; ring
  · rw [if_neg hti, if_neg hti]
    simp only [Matrix.sub_apply, Matrix.add_apply]; ring

/-- K1: trace of a cyclic word kernel against a product of labelled operators. -/
lemma trace_CK {d m : ℕ} (P N B : Fin (m+1) → Mat d) (t : Fin (m+1) → Bool) :
    (tensor (m+1) (fun i => Xl (P i) (N i)) * CK B t).trace =
      ((List.ofFn (fun i => B i * (if t i then N i else P i))).prod).trace := by
  rw [label_sum_gen, Matrix.trace_mul_comm, Matrix.mul_assoc, ← kron_mul, trace_shift]

/-- number of `true` entries -/
def nt {k : ℕ} (τ : Fin k → Bool) : ℕ := ∑ i, if τ i then 1 else 0

lemma coeff_linprod {R : Type*} [Ring R] : ∀ (k : ℕ) (u v : Fin k → R) (j : ℕ),
    ((List.ofFn (fun i => Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i))).prod).coeff j =
      ∑ τ : Fin k → Bool, if nt τ = j then (List.ofFn (fun i => if τ i then v i else u i)).prod else 0
  | 0, u, v, j => by
    simp only [List.ofFn_zero, List.prod_nil, nt, Finset.univ_eq_empty, Finset.sum_empty]
    rw [Fintype.sum_unique]
    rw [Polynomial.coeff_one]
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  | k+1, u, v, j => by
    rw [List.ofFn_succ, List.prod_cons]
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc]
    rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have hnt : ∀ (b : Bool) (τ' : Fin k → Bool), nt (Fin.cons b τ' : Fin (k+1) → Bool) =
        (if b then 1 else 0) + nt τ' := by
      intro b τ'; simp only [nt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [hnt, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons, if_true,
      Bool.false_eq_true, if_false, zero_add]
    rw [coeff_linprod k (fun i => u i.succ) (fun i => v i.succ) j]
    rw [add_comm]
    congr 1
    · cases j with
      | zero =>
        rw [Polynomial.coeff_X_mul_zero]
        symm; refine Finset.sum_eq_zero (fun τ' _ => ?_)
        rw [if_neg]; omega
      | succ j =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
          coeff_linprod k (fun i => u i.succ) (fun i => v i.succ) j, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun τ' _ => ?_)
        by_cases h : nt τ' = j
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega), mul_zero]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ' _ => ?_)
      split_ifs <;> simp


lemma word_taylor {d : ℕ} (w : Word d) (X Y E₀ E₁ : Mat d) (j : ℕ) :
    ((wordLine w X Y E₀ E₁).coeff j).trace =
      ∑ τ : Fin w.factors.length → Bool, if nt τ = j then
        ((List.ofFn (fun i : Fin w.factors.length => (w.factors[i]).1 *
          (if τ i then (if (w.factors[i]).2 then E₁ else E₀)
            else (if (w.factors[i]).2 then Y else X)))).prod * w.tail).trace else 0 := by
  unfold wordLine
  rw [Polynomial.coeff_mul_C]
  have hf : ∀ At : Mat d × Bool, Polynomial.C At.1 *
      (Polynomial.C (if At.2 then Y else X) + Polynomial.X * Polynomial.C (if At.2 then E₁ else E₀)) =
      Polynomial.C (At.1 * (if At.2 then Y else X)) +
        Polynomial.X * Polynomial.C (At.1 * (if At.2 then E₁ else E₀)) := by
    intro At
    rw [mul_add, ← Polynomial.C_mul, ← mul_assoc, (Polynomial.commute_X (Polynomial.C At.1)).eq.symm,
      mul_assoc, ← Polynomial.C_mul]
  simp only [hf]
  rw [← List.ofFn_getElem_eq_map]
  rw [coeff_linprod, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  split_ifs with h
  · congr 3; exact congrArg List.ofFn (funext fun i => by simp only [Fin.getElem_fin]; split_ifs <;> rfl)
  · simp


lemma wordKernel_CK {d : ℕ} (w : Word d) :
    wordKernel w w.factors.length =
      CK (fun i : Fin w.factors.length => if i.val = 0 then w.tail * (w.factors[i]).1 else (w.factors[i]).1)
        (fun i => (w.factors[i]).2) := by
  have h1 : ∀ i : Fin w.factors.length, w.factors[i.val]?.getD (1, false) = w.factors[i] := by
    intro i; rw [List.getElem?_eq_getElem i.isLt]; rfl
  unfold wordKernel CK
  refine (if_pos rfl).trans ?_
  funext x y
  simp only [h1]

lemma CK_form {d k : ℕ} (hk : 0 < k) (P N F : Fin k → Mat d) (tl : Mat d) (t : Fin k → Bool) :
    (tensor k (fun i => Xl (P i) (N i)) * CK (fun i => if i.val = 0 then tl * F i else F i) t).trace =
      ((List.ofFn (fun i => F i * (if t i then N i else P i))).prod * tl).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [trace_CK, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
  simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm tl]
  simp only [Matrix.mul_assoc]

lemma word_form {d : ℕ} (w : Word d) (hk : 0 < w.factors.length)
    (τ : Fin w.factors.length → Bool) (E₀ E₁ X Y : Mat d) :
    (tensor w.factors.length (fun i => if τ i then Xl E₀ E₁ else Xl X Y) *
      wordKernel w w.factors.length).trace =
    ((List.ofFn (fun i : Fin w.factors.length => (w.factors[i]).1 *
          (if τ i then (if (w.factors[i]).2 then E₁ else E₀)
            else (if (w.factors[i]).2 then Y else X)))).prod * w.tail).trace := by
  have hX : (fun i : Fin w.factors.length => if τ i then Xl E₀ E₁ else Xl X Y) =
      fun i => Xl (if τ i then E₀ else X) (if τ i then E₁ else Y) := by
    funext i; split_ifs <;> rfl
  rw [hX, wordKernel_CK, CK_form hk]
  congr 3
  exact congrArg List.ofFn (funext fun i => by split_ifs <;> rfl)


section symtools
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma permOp_mul' {k : ℕ} (π π' : Equiv.Perm (Fin k)) :
    permutationOp (ι := ι) π * permutationOp π' = permutationOp (π * π') := by
  ext x y
  simp only [Matrix.mul_apply, permutationOp, OptimalSpectrum.Entangled.permOp, Matrix.of_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ ⇑π'.symm)]
  · simp only [if_true]
    have : y ∘ ⇑(π * π').symm = (y ∘ ⇑π'.symm) ∘ ⇑π.symm := by
      funext a; simp [Equiv.Perm.mul_def]
    rw [this]
  · intro u _ hu; rw [if_neg hu]
  · simp

lemma permOp_conj {k : ℕ} (π : Equiv.Perm (Fin k)) :
    (permutationOp (ι := ι) π)ᴴ = permutationOp π⁻¹ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, permutationOp, OptimalSpectrum.Entangled.permOp,
    Matrix.of_apply, apply_ite star, star_one, star_zero]
  have : (y = x ∘ ⇑π.symm) ↔ (x = y ∘ ⇑(π⁻¹).symm) := by
    constructor
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
  by_cases h : y = x ∘ ⇑π.symm
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

lemma permOp_unitary {k : ℕ} (π : Equiv.Perm (Fin k)) :
    permutationOp (ι := ι) π * (permutationOp π)ᴴ = 1 := by
  rw [permOp_conj, permOp_mul', mul_inv_cancel]
  ext x y
  simp only [permutationOp, OptimalSpectrum.Entangled.permOp, Matrix.of_apply, Matrix.one_apply]
  have : (Equiv.symm (1 : Equiv.Perm (Fin k)) : Fin k → Fin k) = id := by
    funext i; rfl
  rw [this, Function.comp_id]

lemma tensor_perm {k : ℕ} (G : Fin k → Matrix ι ι ℂ) (π : Equiv.Perm (Fin k)) :
    (permutationOp (ι := ι) π)ᴴ * tensor k G * permutationOp π = tensor k (fun i => G (π i)) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permutationOp,
    OptimalSpectrum.Entangled.permOp, Matrix.of_apply, tensor,
    OptimalSpectrum.Entangled.kronFamily]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  first
  | (rw [← Equiv.prod_comp π.symm (fun i => G (π i) (x i) (y i))]; simp)
  | (rw [← Equiv.prod_comp π (fun j => G j ((x ∘ ⇑π.symm) j) ((y ∘ ⇑π.symm) j))]; simp)

def glueEquiv {α : Type*} {k j : ℕ} (hjk : j ≤ k) : (Fin j → α) × (Fin (k-j) → α) ≃ (Fin k → α) where
  toFun p := glueGen p.1 p.2
  invFun u := (fun i => u (Fin.castLE hjk i), fun i => u ⟨i.val + j, by omega⟩)
  left_inv p := by
    obtain ⟨x, z⟩ := p
    ext i
    · simp [glueGen, Fin.castLE]
    · simp only [glueGen]
      rw [dif_neg (by simp)]
      congr 1; ext; simp
  right_inv u := by
    funext i
    simp only [glueGen]
    split_ifs with h
    · rfl
    · congr 1; ext; simp; omega

lemma prod_split {M : Type*} [CommMonoid M] {k j : ℕ} (hjk : j ≤ k) (f : Fin k → M) :
    ∏ i, f i = (∏ i : Fin j, f (Fin.castLE hjk i)) * ∏ i : Fin (k-j), f ⟨i.val + j, by omega⟩ := by
  let e : Fin j ⊕ Fin (k-j) ≃ Fin k := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hjk))
  have he1 : ∀ i : Fin j, e (Sum.inl i) = Fin.castLE hjk i := by intro i; ext; simp [e]
  have he2 : ∀ i : Fin (k-j), e (Sum.inr i) = ⟨i.val + j, by omega⟩ := by
    intro i; ext; simp [e]; omega
  rw [← Fintype.prod_equiv e (fun s => f (e s)) f (fun _ => rfl), Fintype.prod_sum_type]
  simp only [he1, he2]

lemma glue_castLE {α : Type*} {k j : ℕ} (hjk : j ≤ k) (x : Fin j → α) (z : Fin (k-j) → α) (i : Fin j) :
    glueGen (k := k) x z (Fin.castLE hjk i) = x i := by
  simp [glueGen, Fin.castLE]

lemma glue_shift {α : Type*} {k j : ℕ} (x : Fin j → α) (z : Fin (k-j) → α) (i : Fin (k-j)) :
    glueGen (k := k) x z ⟨i.val + j, by omega⟩ = z i := by
  simp only [glueGen]; rw [dif_neg (by simp)]; congr 1; ext; simp



lemma trace_contraction {k j : ℕ} (hjk : j ≤ k) (Z ω : Matrix ι ι ℂ)
    (h : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (tensor k (fun i => if i.val < j then Z else ω) * h).trace =
      (tensor j (fun _ => Z) * contractionGen ω k j h).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, contractionGen, powerState]
  rw [← (glueEquiv (α := ι) hjk).sum_comp, Fintype.sum_prod_type]
  simp only [← (glueEquiv (α := ι) hjk).sum_comp (fun v => _ * h v _), Fintype.sum_prod_type]
  simp only [glueEquiv, Equiv.coe_fn_mk]
  have hprod : ∀ (u1 v1 : Fin j → ι) (u2 v2 : Fin (k-j) → ι),
      (∏ l : Fin k, (if l.val < j then Z else ω) (glueGen (k := k) u1 u2 l) (glueGen (k := k) v1 v2 l)) =
      (∏ i, Z (u1 i) (v1 i)) * ∏ i, ω (u2 i) (v2 i) := by
    intro u1 v1 u2 v2
    rw [prod_split hjk]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [glue_castLE, glue_castLE, if_pos (by simp)]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [glue_shift, glue_shift, if_neg (by simp)]
  simp only [hprod]
  refine Finset.sum_congr rfl (fun u1 _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v2 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u2 _ => ?_)
  ring

lemma card_nt_true {k : ℕ} (τ : Fin k → Bool) : Fintype.card {i // τ i = true} = nt τ := by
  rw [Fintype.card_subtype, Finset.card_filter]; rfl

lemma sym_reduce {k j : ℕ} (hjk : j ≤ k) (Z ω : Matrix ι ι ℂ) (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * h * (permutationOp π)ᴴ = h)
    (τ : Fin k → Bool) (hτ : nt τ = j) :
    (tensor k (fun i => if τ i then Z else ω) * h).trace =
      (tensor k (fun i => if i.val < j then Z else ω) * h).trace := by
  let e1 : {l : Fin k // l.val < j} ≃ Fin j :=
    { toFun := fun l => ⟨l.1.val, l.2⟩
      invFun := fun i => ⟨Fin.castLE hjk i, by simp⟩
      left_inv := fun l => by ext; simp
      right_inv := fun i => by ext; simp }
  have hc : Fintype.card {l : Fin k // l.val < j} = Fintype.card {i // τ i = true} := by
    rw [Fintype.card_congr e1, Fintype.card_fin, card_nt_true, hτ]
  let e0 : {l : Fin k // l.val < j} ≃ {i // τ i = true} := Fintype.equivOfCardEq hc
  set π := e0.extendSubtype
  have hπ : ∀ l, τ (π l) = decide (l.val < j) := by
    intro l
    by_cases hl : l.val < j
    · rw [Equiv.extendSubtype_apply_of_mem e0 l hl, decide_eq_true hl]; exact (e0 ⟨l, hl⟩).2
    · rw [Equiv.extendSubtype_apply_of_not_mem e0 l hl, decide_eq_false hl]
      have := (e0.toCompl ⟨l, hl⟩).2
      simpa using this
  have hT : tensor k (fun i => if i.val < j then Z else ω) =
      (permutationOp (ι := ι) π)ᴴ * tensor k (fun i => if τ i then Z else ω) * permutationOp π := by
    rw [tensor_perm]
    congr 1; funext l
    rw [hπ l]; by_cases hl : l.val < j <;> simp [hl]
  rw [hT]
  set P := permutationOp (ι := ι) π
  have hP : P * Pᴴ = 1 := permOp_unitary π
  calc (tensor k (fun i => if τ i then Z else ω) * h).trace
      = (tensor k (fun i => if τ i then Z else ω) * (P * h * Pᴴ)).trace := by rw [hsym π]
    _ = (Pᴴ * tensor k (fun i => if τ i then Z else ω) * P * h).trace := by
        rw [Matrix.trace_mul_comm (Pᴴ * _ * P)]
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm P]
        simp only [Matrix.mul_assoc]

lemma card_nt : ∀ (k j : ℕ), ∑ τ : Fin k → Bool, (if nt τ = j then (1:ℂ) else 0) = (Nat.choose k j : ℂ)
  | 0, j => by
    rw [Fintype.sum_unique]
    simp only [nt, Finset.univ_eq_empty, Finset.sum_empty]
    cases j <;> simp
  | k+1, j => by
    rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have hnt : ∀ (b : Bool) (τ' : Fin k → Bool), nt (Fin.cons b τ' : Fin (k+1) → Bool) =
        (if b then 1 else 0) + nt τ' := by
      intro b τ'; simp only [nt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [hnt, if_true, Bool.false_eq_true, if_false, zero_add]
    cases j with
    | zero =>
      have : ∀ τ' : Fin k → Bool, ¬ (1 + nt τ' = 0) := by intro τ'; omega
      simp only [this, if_false, Finset.sum_const_zero, zero_add]
      rw [card_nt k 0]; simp
    | succ j =>
      have : ∀ τ' : Fin k → Bool, (1 + nt τ' = j + 1) ↔ nt τ' = j := by intro τ'; omega
      simp only [this]
      rw [card_nt k j, card_nt k (j+1), Nat.choose_succ_succ]; push_cast; ring

lemma contraction_count {k j : ℕ} (hjk : j ≤ k) (Z ω : Matrix ι ι ℂ)
    (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * h * (permutationOp π)ᴴ = h) :
    (Nat.choose k j : ℂ) * (tensor j (fun _ => Z) * contractionGen ω k j h).trace =
      ∑ τ : Fin k → Bool, if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * h).trace else 0 := by
  have : ∀ τ : Fin k → Bool, (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * h).trace else 0) =
      (if nt τ = j then (1:ℂ) else 0) * (tensor j (fun _ => Z) * contractionGen ω k j h).trace := by
    intro τ
    by_cases hτ : nt τ = j
    · rw [if_pos hτ, if_pos hτ, one_mul, sym_reduce hjk Z ω h hsym τ hτ, trace_contraction hjk]
    · rw [if_neg hτ, if_neg hτ, zero_mul]
  simp only [this, ← Finset.sum_mul, card_nt]

lemma nt_comp {k : ℕ} (τ : Fin k → Bool) (π : Equiv.Perm (Fin k)) : nt (fun i => τ (π i)) = nt τ := by
  unfold nt; exact Equiv.sum_comp π (fun i => if τ i then 1 else 0)

lemma sym_sum {k j : ℕ} (Z ω : Matrix ι ι ℂ) (V : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    ∑ τ : Fin k → Bool, (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * symmetrize V).trace else 0) =
      ∑ τ : Fin k → Bool, (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * V).trace else 0) := by
  unfold symmetrize
  have hπ : ∀ π : Equiv.Perm (Fin k), ∑ τ : Fin k → Bool, (if nt τ = j then
      (tensor k (fun i => if τ i then Z else ω) * (permutationOp π * V * (permutationOp π)ᴴ)).trace else 0) =
      ∑ τ : Fin k → Bool, (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * V).trace else 0) := by
    intro π
    have h1 : ∀ τ : Fin k → Bool, (tensor k (fun i => if τ i then Z else ω) *
        (permutationOp π * V * (permutationOp π)ᴴ)).trace =
        (tensor k (fun i => if τ (π i) then Z else ω) * V).trace := by
      intro τ
      rw [← tensor_perm (fun i => if τ i then Z else ω) π]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp only [h1]
    let eτ : (Fin k → Bool) ≃ (Fin k → Bool) :=
      { toFun := fun τ i => τ (π i), invFun := fun τ i => τ (π.symm i),
        left_inv := fun τ => by funext i; simp, right_inv := fun τ => by funext i; simp }
    have := Equiv.sum_comp eτ (fun τ => if nt τ = j then (tensor k (fun i => if τ i then Z else ω) * V).trace else 0)
    rw [← this]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simp only [eτ, Equiv.coe_fn_mk, nt_comp]
  have h2 : ∀ τ : Fin k → Bool, (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) *
      (((k.factorial : ℂ))⁻¹ • ∑ π : Equiv.Perm (Fin k), permutationOp π * V * (permutationOp π)ᴴ)).trace else 0) =
      ((k.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin k), (if nt τ = j then (tensor k (fun i => if τ i then Z else ω) *
        (permutationOp π * V * (permutationOp π)ᴴ)).trace else 0) := by
    intro τ
    split_ifs
    · rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum, smul_eq_mul]
    · simp
  simp only [h2]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hπ, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos k).ne'), one_mul]

lemma trace_hermPart {κ : Type*} [Fintype κ] (M V : Matrix κ κ ℂ) :
    (M * hermPart V).trace = (2:ℂ)⁻¹ * ((M * V).trace + star ((Mᴴ * V).trace)) := by
  unfold hermPart
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, smul_eq_mul]
  congr 2
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]

lemma symmetrize_sym {k : ℕ} (V : Matrix (Fin k → ι) (Fin k → ι) ℂ) (π : Equiv.Perm (Fin k)) :
    permutationOp π * symmetrize V * (permutationOp π)ᴴ = symmetrize V := by
  have this : ∀ π' : Equiv.Perm (Fin k), permutationOp π * (permutationOp π' * V * (permutationOp π')ᴴ) *
      (permutationOp π)ᴴ = permutationOp (π * π') * V * (permutationOp (π * π'))ᴴ := by
    intro π'
    rw [← permOp_mul', Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hsum : ∑ π' : Equiv.Perm (Fin k), permutationOp π * (permutationOp π' * V * (permutationOp π')ᴴ) *
      (permutationOp π)ᴴ = ∑ π' : Equiv.Perm (Fin k), permutationOp (ι := ι) π' * V * (permutationOp π')ᴴ := by
    simp only [this]
    exact Equiv.sum_comp (Equiv.mulLeft π) (fun π' => permutationOp (ι := ι) π' * V * (permutationOp π')ᴴ)
  unfold symmetrize
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hsum]

lemma hermPart_sym {k : ℕ} (V : Matrix (Fin k → ι) (Fin k → ι) ℂ) (π : Equiv.Perm (Fin k))
    (hV : permutationOp π * V * (permutationOp π)ᴴ = V) :
    permutationOp π * hermPart V * (permutationOp π)ᴴ = hermPart V := by
  have h2 : permutationOp π * Vᴴ * (permutationOp π)ᴴ = Vᴴ := by
    have := congrArg Matrix.conjTranspose hV
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  unfold hermPart
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hV, h2]

lemma expressionKernel_sym {d k : ℕ} (g : TraceExpression d) (π : Equiv.Perm (Fin k)) :
    permutationOp π * expressionKernel g k * (permutationOp π)ᴴ = expressionKernel g k := by
  unfold expressionKernel
  exact hermPart_sym _ π (symmetrize_sym _ π)

end symtools

lemma Xl_conj {d : ℕ} (P N : Mat d) : (Xl P N)ᴴ = Xl Pᴴ Nᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Xl]
  by_cases h : x.1 = y.1
  · rw [if_pos h.symm, if_pos h]
    by_cases hy : y.1
    · rw [h] at *; simp [hy, Matrix.conjTranspose_apply, star_mul']
    · rw [h] at *; simp [hy, Matrix.conjTranspose_apply, star_mul']
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

lemma tensor_conj' {ι : Type*} [Fintype ι] {k : ℕ} (A : Fin k → Matrix ι ι ℂ) :
    (tensor k A)ᴴ = tensor k (fun i => (A i)ᴴ) := by
  ext x y
  simp [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.conjTranspose_apply, star_prod]

lemma foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | (b :: l), a => by
    have ih := foldl_max_ge l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left a b) ih.1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) ih.1
    · exact ih.2 x hx

lemma len_le_deg {d : ℕ} (g : TraceExpression d) (w : Word d) (hw : w ∈ g.words) :
    w.factors.length ≤ expressionDegree g :=
  (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)



lemma wordKernel_ne {d k : ℕ} {w : Word d} (h : w.factors.length ≠ k) : wordKernel w k = 0 := by
  unfold wordKernel; exact if_neg h


lemma list_finset_swap {α β : Type*} (s : Finset β) (l : List α) (f : β → α → ℂ) :
    ∑ k ∈ s, (l.map (f k)).sum = (l.map (fun w => ∑ k ∈ s, f k w)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

lemma trace_list_gen {κ α : Type*} [Fintype κ] (M : Matrix κ κ ℂ) (l : List α) (f : α → Matrix κ κ ℂ) :
    (M * (l.map f).sum).trace = (l.map (fun w => (M * f w).trace)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Matrix.mul_add, Matrix.trace_add, ih]

lemma nt_le {k : ℕ} (τ : Fin k → Bool) : nt τ ≤ k := by
  unfold nt
  calc ∑ i, (if τ i then 1 else 0) ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = k := by simp

lemma labelled_herm {d : ℕ} {ρ σ : Mat d} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (labelledState ρ σ)ᴴ = labelledState ρ σ := by
  rw [← Xl_labelled, Xl_conj]
  congr 1
  · unfold plus; rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hρ.eq, hσ.eq]; simp
  · unfold minus; rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hρ.eq, hσ.eq]; simp

/-- Σ over selections of the form of the word part of the degree-`k` kernel. -/
lemma words_form {d k j : ℕ} (hj : 1 ≤ j) (ρ σ : Mat d) (g : TraceExpression d) (E₀ E₁ : Mat d) :
    ∑ τ : Fin k → Bool, (if nt τ = j then
      (tensor k (fun i => if τ i then Xl E₀ E₁ else labelledState ρ σ) *
        (g.words.map (fun w => wordKernel w k)).sum).trace else 0) =
    (g.words.map (fun w => if w.factors.length = k then
      ((wordLine w (plus ρ σ) (minus ρ σ) E₀ E₁).coeff j).trace else 0)).sum := by
  have h1 : ∀ τ : Fin k → Bool, (if nt τ = j then
      (tensor k (fun i => if τ i then Xl E₀ E₁ else labelledState ρ σ) *
        (g.words.map (fun w => wordKernel w k)).sum).trace else 0) =
      (g.words.map (fun w => if nt τ = j then
        (tensor k (fun i => if τ i then Xl E₀ E₁ else labelledState ρ σ) * wordKernel w k).trace else 0)).sum := by
    intro τ
    split_ifs
    · rw [trace_list_gen]
    · simp
  simp only [h1]
  rw [list_finset_swap]
  congr 1
  refine List.map_congr_left (fun w _ => ?_)
  by_cases hk : w.factors.length = k
  · subst hk
    rw [if_pos rfl, word_taylor]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    split_ifs with hτ
    · rw [← Xl_labelled, word_form w (by have := nt_le τ; omega)]
    · rfl
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun τ _ => ?_)
    rw [wordKernel_ne hk, Matrix.mul_zero, Matrix.trace_zero]; simp


lemma tensor_ite_conj {ι : Type*} [Fintype ι] {k : ℕ} (τ : Fin k → Bool) (Z ω : Matrix ι ι ℂ)
    (hω : ωᴴ = ω) :
    (tensor k (fun i => if τ i then Z else ω))ᴴ = tensor k (fun i => if τ i then Zᴴ else ω) := by
  rw [tensor_conj']; congr 1; funext i; split_ifs <;> simp [hω]

lemma form_effective {d : ℕ} (ρ σ : Mat d) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : TraceExpression d) {j : ℕ} (hj : 1 ≤ j) (E₀ E₁ : Mat d) :
    (tensor j (fun _ => Xl E₀ E₁) * effectiveKernelGen (labelledState ρ σ) (expressionDegree g)
      (fun k => expressionKernel g k) j).trace =
    (2:ℂ)⁻¹ * (taylor g (plus ρ σ) (minus ρ σ) j E₀ E₁ +
      star (taylor g (plus ρ σ) (minus ρ σ) j E₀ᴴ E₁ᴴ)) := by
  set L := labelledState ρ σ with hL
  have hLH : Lᴴ = L := labelled_herm hρ hσ
  set D := expressionDegree g
  -- the word sums
  set Φ : Mat d → Mat d → ℕ → ℂ := fun A B k => (g.words.map (fun w => if w.factors.length = k then
      ((wordLine w (plus ρ σ) (minus ρ σ) A B).coeff j).trace else 0)).sum with hΦ
  have hk : ∀ k ∈ Finset.Icc j D,
      (Nat.choose k j : ℂ) * (tensor j (fun _ => Xl E₀ E₁) * contractionGen L k j (expressionKernel g k)).trace =
      (2:ℂ)⁻¹ * (Φ E₀ E₁ k + star (Φ E₀ᴴ E₁ᴴ k)) := by
    intro k hk
    have hjk : j ≤ k := (Finset.mem_Icc.1 hk).1
    rw [contraction_count hjk _ _ _ (fun π => expressionKernel_sym g π)]
    unfold expressionKernel
    simp only [trace_hermPart, tensor_ite_conj _ _ _ hLH, Xl_conj]
    have hsplit : ∀ τ : Fin k → Bool, (if nt τ = j then (2:ℂ)⁻¹ *
        ((tensor k (fun i => if τ i then Xl E₀ E₁ else L) *
          symmetrize ((g.words.map (fun w => wordKernel w k)).sum)).trace +
        star ((tensor k (fun i => if τ i then Xl E₀ᴴ E₁ᴴ else L) *
          symmetrize ((g.words.map (fun w => wordKernel w k)).sum)).trace)) else 0) =
        (2:ℂ)⁻¹ * ((if nt τ = j then (tensor k (fun i => if τ i then Xl E₀ E₁ else L) *
          symmetrize ((g.words.map (fun w => wordKernel w k)).sum)).trace else 0) +
          star (if nt τ = j then (tensor k (fun i => if τ i then Xl E₀ᴴ E₁ᴴ else L) *
          symmetrize ((g.words.map (fun w => wordKernel w k)).sum)).trace else 0)) := by
      intro τ; split_ifs <;> simp
    simp only [hsplit]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← star_sum]
    rw [sym_sum, sym_sum, words_form hj, words_form hj]
  unfold effectiveKernelGen
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, Finset.sum_add_distrib, ← star_sum]
  -- collapse the k-sums
  have hcol : ∀ A B : Mat d, ∑ k ∈ Finset.Icc j D, Φ A B k = taylor g (plus ρ σ) (minus ρ σ) j A B := by
    intro A B
    simp only [hΦ]
    rw [list_finset_swap]
    unfold taylor
    rw [if_neg (by omega), zero_add]
    congr 1
    refine List.map_congr_left (fun w hw => ?_)
    rw [Finset.sum_ite_eq]
    by_cases hmem : w.factors.length ∈ Finset.Icc j D
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      have hlen := len_le_deg g w hw
      have hlt : w.factors.length < j := by
        rw [Finset.mem_Icc] at hmem; omega
      rw [word_taylor]
      symm
      refine Finset.sum_eq_zero (fun τ _ => ?_)
      rw [if_neg]
      have := nt_le τ; omega
  rw [hcol, hcol]


section polar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stdBasis_tensor {k : ℕ} (x y : Fin k → ι) :
    tensor k (fun i => Matrix.single (x i) (y i) (1:ℂ)) = Matrix.single x y (1:ℂ) := by
  ext u v
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.single_apply]
  rw [Fintype.prod_boole]
  by_cases h1 : x = u <;> by_cases h2 : y = v
  · subst h1; subst h2; simp
  · rw [if_neg, if_neg]
    · rintro ⟨-, h⟩; exact h2 h
    · intro h; exact h2 (funext fun i => (h i).2)
  · rw [if_neg, if_neg]
    · rintro ⟨h, -⟩; exact h1 h
    · intro h; exact h1 (funext fun i => (h i).1)
  · rw [if_neg, if_neg]
    · rintro ⟨h, -⟩; exact h1 h
    · intro h; exact h1 (funext fun i => (h i).1)

lemma sum_pair {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (a0 : α) (b0 : β) (f : α → β → M) :
    ∑ a, ∑ b, (if a = a0 ∧ b = b0 then f a b else 0) = f a0 b0 := by
  rw [Finset.sum_eq_single a0 (fun a _ ha => Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1)))
    (by simp)]
  rw [Finset.sum_eq_single b0 (fun b _ hb => if_neg (fun h => hb h.2)) (by simp)]
  simp


lemma tensor_sum_fun {k : ℕ} (c : Fin k → Fin k → ℂ) (Z : Fin k → Matrix ι ι ℂ) :
    tensor k (fun l => ∑ i, c l i • Z i) =
      ∑ f : Fin k → Fin k, (∏ l, c l (f l)) • tensor k (fun l => Z (f l)) := by
  ext x y
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum (fun l i => c l i * Z i (x l) (y l))]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma alt_sum {k : ℕ} (f : Fin k → Fin k) :
    ∑ T : Fin k → Bool, (∏ i, if T i then (1:ℂ) else -1) * (∏ l, if T (f l) then (1:ℂ) else 0) =
      if Function.Surjective f then 1 else 0 := by
  have h1 : ∀ T : Fin k → Bool, (∏ i, if T i then (1:ℂ) else -1) * (∏ l, if T (f l) then (1:ℂ) else 0) =
      ∏ i, ((if T i then (1:ℂ) else -1) * (if (∃ l, f l = i) → T i = true then 1 else 0)) := by
    intro T
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_boole, Fintype.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h i ⟨l, hl⟩; rw [← hl]; exact h l
    · intro h l; exact h (f l) ⟨l, rfl⟩
  simp only [h1]
  rw [← Fintype.prod_sum (fun i b => (if b then (1:ℂ) else -1) *
    (if (∃ l, f l = i) → b = true then 1 else 0))]
  simp only [Fintype.sum_bool, if_true, one_mul, Bool.false_eq_true, if_false]
  by_cases hs : Function.Surjective f
  · rw [if_pos hs]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have := hs i
    simp [this]
  · rw [if_neg hs]
    obtain ⟨i, hi⟩ : ∃ i, ¬ ∃ l, f l = i := by
      by_contra h; push Not at h; exact hs h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi]

lemma polarization {k : ℕ} (W : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * W * (permutationOp π)ᴴ = W)
    (Z : Fin k → Matrix ι ι ℂ) :
    ∑ T : Fin k → Bool, (∏ i, if T i then (1:ℂ) else -1) *
      (tensor k (fun _ => ∑ i, (if T i then (1:ℂ) else 0) • Z i) * W).trace =
    (k.factorial : ℂ) * (tensor k Z * W).trace := by
  simp only [tensor_sum_fun, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ f : Fin k → Fin k, ∑ T : Fin k → Bool, (∏ i, if T i then (1:ℂ) else -1) *
      ((∏ l, if T (f l) then (1:ℂ) else 0) * (tensor k (fun l => Z (f l)) * W).trace) =
      (if Function.Surjective f then 1 else 0) * (tensor k (fun l => Z (f l)) * W).trace := by
    intro f
    rw [← alt_sum f, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun T _ => by ring)
  simp only [h2, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  -- surjective maps are permutations
  have hperm : ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin k => Function.Surjective f),
      (tensor k (fun l => Z (f l)) * W).trace = ∑ π : Equiv.Perm (Fin k), (tensor k (fun l => Z (π l)) * W).trace := by
    symm
    refine Finset.sum_nbij' (fun π => ⇑π)
      (fun f => if hf : Function.Surjective f then Equiv.ofBijective f
        (Finite.surjective_iff_bijective.mp hf) else 1) ?_ ?_ ?_ ?_ ?_
    · intro π _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, π.surjective⟩
    · intro f _; simp
    · intro π _; simp only [π.surjective, dite_true]; ext; simp
    · intro f hf
      have hf' := (Finset.mem_filter.1 hf).2
      simp [hf']
    · intro π _; rfl
  rw [hperm]
  have hinv : ∀ π : Equiv.Perm (Fin k), (tensor k (fun l => Z (π l)) * W).trace = (tensor k Z * W).trace := by
    intro π
    rw [← tensor_perm Z π]
    set P := permutationOp (ι := ι) π
    have hP : P * Pᴴ = 1 := permOp_unitary π
    calc (Pᴴ * tensor k Z * P * W).trace = (tensor k Z * (P * W * Pᴴ)).trace := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hsym π]
  simp only [hinv, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end polar


lemma Xl_sum {d k : ℕ} (c : Fin k → ℂ) (P N : Fin k → Mat d) :
    ∑ i, c i • Xl (P i) (N i) = Xl (∑ i, c i • P i) (∑ i, c i • N i) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Xl]
  by_cases h : x.1 = y.1
  · simp only [if_pos h]
    by_cases hx : x.1
    · simp only [hx, if_true, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    · simp only [hx, Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
  · simp [h]

lemma half_lemmas (z : ℂ) : (2:ℂ)⁻¹ * (z - -z) = z ∧ (2:ℂ)⁻¹ * (z + z) = z ∧
    (2:ℂ)⁻¹ * (z - z) = 0 ∧ (2:ℂ)⁻¹ * (z + -z) = 0 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

lemma Xl_single {d : ℕ} (a b : Bool × Fin d) (hab : a.1 = b.1) :
    Xl (Matrix.single a.2 b.2 (1:ℂ)) (if a.1 then -Matrix.single a.2 b.2 (1:ℂ) else Matrix.single a.2 b.2 (1:ℂ)) =
      Matrix.single a b (1:ℂ) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only at hab
  subst hab
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [Xl]
  by_cases hxy : x1 = y1
  · subst hxy
    rw [if_pos rfl]
    set z := (Matrix.single a2 b2 (1:ℂ)) x2 y2 with hz
    cases a1 <;> cases x1 <;>
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, if_true, if_false,
        Bool.false_eq_true, ← hz, (half_lemmas z).1, (half_lemmas z).2.1, (half_lemmas z).2.2.1,
        (half_lemmas z).2.2.2] <;>
      simp [hz, Matrix.single_apply]
  · rw [if_neg hxy]
    simp only [Matrix.single_apply, Prod.mk.injEq]
    by_cases h1 : a1 = x1
    · have : ¬ (a1 = y1) := by rw [h1]; exact hxy
      simp [this]
    · simp [h1]

lemma kernel_unique {d k : ℕ} (W : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * W * (permutationOp π)ᴴ = W)
    (hdiag : ∀ x y, (fun i => (x i).1) ≠ (fun i => (y i).1) → W x y = 0)
    (h0 : ∀ P N : Mat d, (tensor k (fun _ => Xl P N) * W).trace = 0) : W = 0 := by
  have hmulti : ∀ P N : Fin k → Mat d, (tensor k (fun i => Xl (P i) (N i)) * W).trace = 0 := by
    intro P N
    have hpol := polarization W hsym (fun i => Xl (P i) (N i))
    have hzero : ∀ T : Fin k → Bool, (tensor k (fun _ => ∑ i, (if T i then (1:ℂ) else 0) •
        Xl (P i) (N i)) * W).trace = 0 := by
      intro T; rw [Xl_sum]; exact h0 _ _
    simp only [hzero, mul_zero, Finset.sum_const_zero] at hpol
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    exact (mul_eq_zero.1 hpol.symm).resolve_left hf
  ext x y
  simp only [Matrix.zero_apply]
  by_cases hl : (fun i => (x i).1) = (fun i => (y i).1)
  · have hl' : ∀ i, (y i).1 = (x i).1 := fun i => (congrFun hl i).symm
    have := hmulti (fun i => Matrix.single (y i).2 (x i).2 (1:ℂ))
      (fun i => if (y i).1 then -Matrix.single (y i).2 (x i).2 (1:ℂ) else Matrix.single (y i).2 (x i).2 (1:ℂ))
    simp only [Xl_single _ _ (hl' _)] at this
    rw [stdBasis_tensor] at this
    rw [← this]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single y (fun b _ hb => Finset.sum_eq_zero (fun c _ => if_neg (fun h => hb h.1.symm)))
      (by simp)]
    rw [Finset.sum_eq_single x (fun b _ hb => if_neg (fun h => hb h.2.symm)) (by simp)]
    simp
  · exact hdiag x y hl


section structure_lemmas
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conj_apply {k : ℕ} (π : Equiv.Perm (Fin k)) (M : Matrix (Fin k → ι) (Fin k → ι) ℂ) (x y : Fin k → ι) :
    ((permutationOp (ι := ι) π * M * (permutationOp (ι := ι) π)ᴴ : Matrix (Fin k → ι) (Fin k → ι) ℂ)) x y =
      M (x ∘ π) (y ∘ π) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permutationOp,
    OptimalSpectrum.Entangled.permOp, Matrix.of_apply, apply_ite star, star_one, star_zero,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  have h1 : ∀ u : Fin k → ι, (x = u ∘ ⇑π.symm) ↔ (u = x ∘ ⇑π) := by
    intro u; constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  have h2 : ∀ v : Fin k → ι, (y = v ∘ ⇑π.symm) ↔ (v = y ∘ ⇑π) := by
    intro v; constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma sym_of_apply {k : ℕ} (M : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (h : ∀ (π : Equiv.Perm (Fin k)) x y, M (x ∘ π) (y ∘ π) = M x y) :
    ∀ π : Equiv.Perm (Fin k), permutationOp π * M * (permutationOp π)ᴴ = M := by
  intro π; ext x y; rw [conj_apply, h]

lemma apply_of_sym {k : ℕ} (M : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (h : ∀ π : Equiv.Perm (Fin k), permutationOp π * M * (permutationOp π)ᴴ = M)
    (π : Equiv.Perm (Fin k)) (x y : Fin k → ι) : M (x ∘ π) (y ∘ π) = M x y := by
  have := conj_apply π M x y
  rw [h π] at this
  exact this.symm

lemma contraction_sym {k j : ℕ} (hjk : j ≤ k) (ω : Matrix ι ι ℂ) (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * h * (permutationOp π)ᴴ = h) :
    ∀ π : Equiv.Perm (Fin j), permutationOp π * contractionGen ω k j h * (permutationOp π)ᴴ =
      contractionGen ω k j h := by
  refine sym_of_apply _ (fun π x y => ?_)
  let e : Fin j ⊕ Fin (k-j) ≃ Fin k := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hjk))
  have he1 : ∀ i : Fin j, e (Sum.inl i) = Fin.castLE hjk i := by intro i; ext; simp [e]
  have he2 : ∀ i : Fin (k-j), e (Sum.inr i) = ⟨i.val + j, by omega⟩ := by
    intro i; ext; simp [e]; omega
  let πt : Equiv.Perm (Fin k) := e.symm.trans ((Equiv.sumCongr π (Equiv.refl _)).trans e)
  have hglue : ∀ (u : Fin j → ι) (z : Fin (k-j) → ι),
      glueGen (k := k) (u ∘ π) z = (glueGen (k := k) u z) ∘ πt := by
    intro u z
    funext i
    obtain ⟨s, rfl⟩ := e.surjective i
    cases s with
    | inl a =>
      simp only [Function.comp_apply, πt, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.sumCongr_apply, Sum.map_inl]
      rw [he1, he1, glue_castLE, glue_castLE]; rfl
    | inr b =>
      simp only [Function.comp_apply, πt, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]
      rw [he2, glue_shift, glue_shift]
  simp only [contractionGen]
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))
  rw [hglue, hglue, apply_of_sym h hsym πt]

lemma effective_sym {D j : ℕ} (ω : Matrix ι ι ℂ) (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ k, ∀ π : Equiv.Perm (Fin k), permutationOp π * h k * (permutationOp π)ᴴ = h k) :
    ∀ π : Equiv.Perm (Fin j), permutationOp π * effectiveKernelGen ω D h j * (permutationOp π)ᴴ =
      effectiveKernelGen ω D h j := by
  intro π
  unfold effectiveKernelGen
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul,
    contraction_sym (Finset.mem_Icc.1 hk).1 ω (h k) (hsym k) π]

end structure_lemmas

/-- label-diagonality -/
def LD {d k : ℕ} (W : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ) : Prop :=
  ∀ x y, (fun i => (x i).1) ≠ (fun i => (y i).1) → W x y = 0

lemma LD_add {d k : ℕ} {V W : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ}
    (hV : LD V) (hW : LD W) : LD (V + W) := fun x y h => by simp [hV x y h, hW x y h]

lemma LD_smul {d k : ℕ} {V : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ} (c : ℂ)
    (hV : LD V) : LD (c • V) := fun x y h => by simp [hV x y h]

lemma LD_sum {d k : ℕ} {S : Type*} (s : Finset S) (V : S → Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ)
    (hV : ∀ a ∈ s, LD (V a)) : LD (∑ a ∈ s, V a) := by
  intro x y h; rw [Matrix.sum_apply]; exact Finset.sum_eq_zero (fun a ha => hV a ha x y h)

lemma LD_conj {d k : ℕ} {V : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ} (hV : LD V) :
    LD Vᴴ := fun x y h => by rw [Matrix.conjTranspose_apply, hV y x (Ne.symm h), star_zero]

lemma LD_hermPart {d k : ℕ} {V : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ} (hV : LD V) :
    LD (hermPart V) := by
  unfold hermPart; exact LD_smul _ (LD_add hV (LD_conj hV))

lemma LD_symmetrize {d k : ℕ} {V : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ} (hV : LD V) :
    LD (symmetrize V) := by
  unfold symmetrize
  refine LD_smul _ (LD_sum _ _ (fun π _ => fun x y h => ?_))
  rw [conj_apply]
  apply hV
  intro h'; apply h; funext i
  have := congrFun h' (π.symm i); simpa using this

lemma LD_CK {d k : ℕ} (B : Fin k → Mat d) (t : Fin k → Bool) : LD (CK B t) := by
  intro x y h; simp [CK, h]

lemma LD_wordKernel {d k : ℕ} (w : Word d) : LD (wordKernel w k) := by
  intro x y h
  by_cases hk : w.factors.length = k
  · subst hk; rw [wordKernel_CK]; exact LD_CK _ _ x y h
  · rw [wordKernel_ne hk]; rfl

lemma LD_expressionKernel {d k : ℕ} (g : TraceExpression d) : LD (expressionKernel g k) := by
  unfold expressionKernel
  refine LD_hermPart (LD_symmetrize ?_)
  have : ∀ l : List (Word d), LD (l.map (fun w => wordKernel w k)).sum := by
    intro l; induction l with
    | nil => intro x y _; simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact LD_add (LD_wordKernel a) ih
  exact this _

lemma LD_contraction {d k j : ℕ} (hjk : j ≤ k) (ω : Matrix (Bool × Fin d) (Bool × Fin d) ℂ)
    {h : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ} (hh : LD h) :
    LD (contractionGen ω k j h) := by
  intro x y hxy
  simp only [contractionGen]
  refine Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun w _ => ?_))
  rw [hh, zero_mul]
  intro h'; apply hxy; funext i
  have := congrFun h' (Fin.castLE hjk i)
  simp only [glue_castLE] at this
  exact this

lemma LD_effective {d D j : ℕ} (ω : Matrix (Bool × Fin d) (Bool × Fin d) ℂ)
    (h : (k : ℕ) → Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ) (hh : ∀ k, LD (h k)) :
    LD (effectiveKernelGen ω D h j) := by
  unfold effectiveKernelGen
  exact LD_sum _ _ (fun k hk => LD_smul _ (LD_contraction (Finset.mem_Icc.1 hk).1 ω (hh k)))


/-- shifting an idempotent through a product -/
lemma q_shift {R : Type*} [Monoid R] (q : R) (hq : q * q = q) :
    ∀ (l : List (R × R)), q * (l.map (fun p => p.1 * (q * p.2 * q))).prod =
      (l.map (fun p => q * p.1 * q * p.2)).prod * q
  | [] => by simp
  | (a, b) :: l => by
    simp only [List.map_cons, List.prod_cons]
    have ih := q_shift q hq l
    calc q * (a * (q * b * q) * (l.map (fun p => p.1 * (q * p.2 * q))).prod)
        = q * a * q * b * (q * (l.map (fun p => p.1 * (q * p.2 * q))).prod) := by
          simp only [mul_assoc]
      _ = q * a * q * b * ((l.map (fun p => q * p.1 * q * p.2)).prod * q) := by rw [ih]
      _ = _ := by simp only [mul_assoc]

lemma subst_wordLine {d : ℕ} (Q : Mat d) (hQ : Q * Q = Q) (w : Word d) (X Y E₀ E₁ : Mat d) :
    wordLine (match w.factors with
      | [] => w
      | (A,t) :: xs => ⟨(A * Q,t) :: xs.map (fun At => (Q * At.1 * Q, At.2)), Q * w.tail⟩) X Y E₀ E₁ =
    wordLine w (Q * X * Q) (Q * Y * Q) (Q * E₀ * Q) (Q * E₁ * Q) := by
  rcases w with ⟨fs, tl⟩
  cases fs with
  | nil => simp [wordLine]
  | cons At xs =>
    obtain ⟨A, t⟩ := At
    simp only [wordLine, List.map_cons, List.prod_cons, List.map_map]
    set q : Polynomial (Mat d) := Polynomial.C Q with hqdef
    have hq : q * q = q := by rw [hqdef, ← Polynomial.C_mul, hQ]
    have hlin : ∀ (U V : Mat d), Polynomial.C (Q * U * Q) + Polynomial.X * Polynomial.C (Q * V * Q) =
        q * (Polynomial.C U + Polynomial.X * Polynomial.C V) * q := by
      intro U V
      simp only [hqdef, Polynomial.C_mul, mul_add, add_mul]
      congr 1
      rw [show Polynomial.X * (Polynomial.C Q * Polynomial.C V * Polynomial.C Q) =
        (Polynomial.X * Polynomial.C Q) * Polynomial.C V * Polynomial.C Q by simp only [mul_assoc],
        (Polynomial.commute_X _).eq]
      simp only [mul_assoc]
    have hite : ∀ (b : Bool) (U V : Mat d), (if b then Q * U * Q else Q * V * Q) = Q * (if b then U else V) * Q := by
      intro b U V; cases b <;> rfl
    simp only [hite, hlin]
    have key := q_shift q hq (xs.map (fun x => (Polynomial.C x.1,
      Polynomial.C (if x.2 then Y else X) + Polynomial.X * Polynomial.C (if x.2 then E₁ else E₀))))
    simp only [List.map_map, Function.comp_def] at key
    have hC3 : ∀ a : Mat d, Polynomial.C (Q * a * Q) = q * Polynomial.C a * q := by
      intro a; simp only [hqdef, Polynomial.C_mul]
    have hA : Polynomial.C (A * Q) = Polynomial.C A * q := by rw [hqdef, Polynomial.C_mul]
    have htl : Polynomial.C (Q * tl) = q * Polynomial.C tl := by rw [hqdef, Polynomial.C_mul]
    simp only [Function.comp_def, hC3, hA, htl]
    simp only [mul_assoc] at key ⊢
    rw [← mul_assoc q (List.prod _) (Polynomial.C tl), key]
    simp only [mul_assoc]



lemma subst_taylor {d : ℕ} (Q : Mat d) (hQ : Q * Q = Q) (g : TraceExpression d) (X Y E₀ E₁ : Mat d) (j : ℕ) :
    taylor (substituteCompression Q g) X Y j E₀ E₁ =
      taylor g (Q * X * Q) (Q * Y * Q) j (Q * E₀ * Q) (Q * E₁ * Q) := by
  rcases g with ⟨c, ws⟩
  simp only [taylor, substituteCompression, List.map_map]
  refine congrArg (fun z => (if j = 0 then c else 0) + z) (congrArg List.sum (List.map_congr_left (fun w _ => ?_)))
  simp only [Function.comp_apply]
  exact congrArg (fun p : Polynomial (Mat d) => (p.coeff j).trace) (subst_wordLine Q hQ w X Y E₀ E₁)

lemma trace_cyc6 {κ : Type*} [Fintype κ] (a b c p q e : Matrix κ κ ℂ) :
    (a * (b * (c * (p * (q * e))))).trace = (q * (e * (a * (b * (c * p))))).trace := by
  have : a * (b * (c * (p * (q * e)))) = (a * (b * (c * p))) * (q * e) := by simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

lemma rep_identity {d m : ℕ} (Q : Mat d) (hQ : Q * Q = Q) (A : Fin (m+2) → Mat d) (Y : Fin (m+1) → Mat d) :
    ((List.ofFn (fun i : Fin (m+1) => A i.castSucc * (Q * Y i * Q))).prod * A (Fin.last (m+1))).trace =
      ((List.ofFn (fun i : Fin (m+1) =>
        (if i.val = 0 then Q * A (Fin.last (m+1)) * A i.castSucc * Q else Q * A i.castSucc * Q) * Y i)).prod).trace := by
  rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
  simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false]
  have key := q_shift Q hQ ((List.ofFn (fun i : Fin m => (A i.succ.castSucc, Y i.succ))))
  simp only [List.map_ofFn, Function.comp_def] at key
  simp only [Fin.castSucc_zero]
  calc (A 0 * (Q * Y 0 * Q) * (List.ofFn fun i : Fin m => A i.succ.castSucc * (Q * Y i.succ * Q)).prod *
        A (Fin.last (m + 1))).trace
      = ((A 0 * (Q * Y 0)) * (Q * (List.ofFn fun i : Fin m => A i.succ.castSucc * (Q * Y i.succ * Q)).prod) *
        A (Fin.last (m + 1))).trace := by simp only [Matrix.mul_assoc]
    _ = ((A 0 * (Q * Y 0)) * ((List.ofFn fun i : Fin m => Q * A i.succ.castSucc * Q * Y i.succ).prod * Q) *
        A (Fin.last (m + 1))).trace := by rw [key]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        exact trace_cyc6 _ _ _ _ _ _


def repF {d m : ℕ} (Q : Mat d) (A : Fin (m+2) → Mat d) : Fin (m+1) → Mat d :=
  fun i => if i.val = 0 then Q * A (Fin.last (m+1)) * A i.castSucc * Q else Q * A i.castSucc * Q

def repKernel {d m Lc : ℕ} (Q : Mat d) (c : Fin Lc → ℂ) (A : Fin Lc → Fin (m+2) → Mat d)
    (t : Fin Lc → Fin (m+1) → Bool) : Matrix (Fin (m+1) → Bool × Fin d) (Fin (m+1) → Bool × Fin d) ℂ :=
  ∑ α, c α • CK (repF Q (A α)) (t α)

lemma repKernel_form {d m Lc : ℕ} (Q : Mat d) (hQ : Q * Q = Q) (c : Fin Lc → ℂ)
    (A : Fin Lc → Fin (m+2) → Mat d) (t : Fin Lc → Fin (m+1) → Bool) (P N : Mat d) :
    (tensor (m+1) (fun _ => Xl P N) * repKernel Q c A t).trace =
      ∑ α, c α * ((List.ofFn (fun i : Fin (m+1) => A α i.castSucc *
        (if t α i then Q * N * Q else Q * P * Q))).prod * A α (Fin.last (m+1))).trace := by
  unfold repKernel
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [trace_CK (fun _ => P) (fun _ => N)]
  have hY : ∀ i : Fin (m+1), (if t α i then Q * N * Q else Q * P * Q) = Q * (if t α i then N else P) * Q := by
    intro i; split_ifs <;> rfl
  simp only [hY]
  rw [rep_identity Q hQ (A α) (fun i => if t α i then N else P)]
  rfl

lemma trace_const_symmetrize {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (Z : Matrix ι ι ℂ)
    (V : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (tensor k (fun _ => Z) * symmetrize V).trace = (tensor k (fun _ => Z) * V).trace := by
  unfold symmetrize
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
  have : ∀ π : Equiv.Perm (Fin k), (tensor k (fun _ => Z) * (permutationOp π * V * (permutationOp π)ᴴ)).trace =
      (tensor k (fun _ => Z) * V).trace := by
    intro π
    have hT : (permutationOp (ι := ι) π)ᴴ * tensor k (fun _ => Z) * permutationOp π = tensor k (fun _ => Z) :=
      tensor_perm (ι := ι) (fun _ => Z) π
    calc (tensor k (fun _ => Z) * (permutationOp π * V * (permutationOp π)ᴴ)).trace
        = ((permutationOp (ι := ι) π)ᴴ * tensor k (fun _ => Z) * permutationOp π * V).trace := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hT]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos k).ne'), one_mul]

theorem identification {d m Lc : ℕ} (ρ σ : Mat d) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (Q : Mat d) (hQ : Q * Q = Q) (g : TraceExpression d)
    (c : Fin Lc → ℂ) (A : Fin Lc → Fin (m+2) → Mat d) (t : Fin Lc → Fin (m+1) → Bool)
    (hrep : ∀ E₀ E₁ : Mat d, taylor g (Q * plus ρ σ * Q) (Q * minus ρ σ * Q) (m+1) E₀ E₁ =
      ∑ α, c α * ((List.ofFn (fun i : Fin (m+1) => A α i.castSucc * (if t α i then E₁ else E₀))).prod *
        A α (Fin.last (m+1))).trace) :
    effectiveKernelGen (labelledState ρ σ) (expressionDegree (substituteCompression Q g))
      (fun k => expressionKernel (substituteCompression Q g) k) (m+1) =
    symmetrize (hermPart (repKernel Q c A t)) := by
  rw [← sub_eq_zero]
  apply kernel_unique
  · intro π
    rw [Matrix.mul_sub, Matrix.sub_mul,
      effective_sym _ _ (fun k π => expressionKernel_sym _ π) π, symmetrize_sym]
  · exact fun x y h => by
      rw [Matrix.sub_apply, LD_effective _ _ (fun k => LD_expressionKernel _) x y h,
        LD_symmetrize (LD_hermPart (by unfold repKernel; exact LD_sum _ _ (fun α _ => LD_smul _ (LD_CK _ _))))
          x y h, sub_zero]
  · intro P N
    rw [Matrix.mul_sub, Matrix.trace_sub, form_effective ρ σ hρ hσ _ (by omega), trace_const_symmetrize,
      trace_hermPart]
    rw [tensor_conj', Xl_conj]
    simp only [subst_taylor Q hQ, hrep, repKernel_form Q hQ]
    exact sub_self _


/-- general permutation kernel -/
def GK {d k : ℕ} (c : Equiv.Perm (Fin k)) (B : Fin k → Mat d) (t : Fin k → Bool) :
    Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ :=
  fun x y => if (fun i => (x i).1) = (fun i => (y i).1) then
    (∏ i, if t i && (x i).1 then (-1 : ℂ) else 1) * ∏ i, B i (x (c i)).2 (y i).2 else 0

lemma CK_eq_GK {d m : ℕ} (B : Fin (m+1) → Mat d) (t : Fin (m+1) → Bool) :
    CK B t = GK (finRotate (m+1)).symm B t := by
  ext x y
  simp only [CK, GK]
  split_ifs with h
  · congr 1
    simp only [Matrix.mul_apply, leftShift, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply,
      ite_mul, one_mul, zero_mul]
    have hiff : ∀ w : Fin (m+1) → Fin d, (∀ i : Fin (m+1), (x i).2 = w ⟨(i.val+1) % (m+1), by
        have := i.isLt; exact Nat.mod_lt _ (by omega)⟩) ↔
        w = fun l => (x ((finRotate (m+1)).symm l)).2 := by
      intro w
      have hrot : ∀ i : Fin (m+1), (⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩ : Fin (m+1)) = finRotate (m+1) i := by
        intro i; rw [finRotate_succ_apply]; ext; simp [Fin.val_add]
      constructor
      · intro hw; funext l
        have := hw ((finRotate (m+1)).symm l)
        rw [hrot, Equiv.apply_symm_apply] at this; exact this.symm
      · intro hw i; rw [hw, hrot]; simp
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rfl

lemma GK_conj {d k : ℕ} (c π : Equiv.Perm (Fin k)) (B : Fin k → Mat d) (t : Fin k → Bool) :
    permutationOp π * GK c B t * (permutationOp π)ᴴ =
      GK (π * c * π⁻¹) (fun l => B (π⁻¹ l)) (fun l => t (π⁻¹ l)) := by
  ext x y
  rw [conj_apply]
  simp only [GK, Function.comp_apply]
  have hlab : ((fun i => (x (π i)).1) = (fun i => (y (π i)).1)) ↔ ((fun i => (x i).1) = (fun i => (y i).1)) := by
    constructor
    · intro h; funext l; have := congrFun h (π⁻¹ l); simpa using this
    · intro h; funext i; exact congrFun h (π i)
  by_cases h : (fun i => (x i).1) = (fun i => (y i).1)
  · rw [if_pos (hlab.2 h), if_pos h]
    congr 1
    · rw [← Equiv.prod_comp π (fun l => if t (π⁻¹ l) && (x l).1 then (-1:ℂ) else 1)]
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    · rw [← Equiv.prod_comp π (fun l => B (π⁻¹ l) (x ((π * c * π⁻¹) l)).2 (y l).2)]
      simp [Equiv.Perm.mul_apply]
  · rw [if_neg (fun h' => h (hlab.1 h')), if_neg h]

lemma GK_adj {d k : ℕ} (c : Equiv.Perm (Fin k)) (B : Fin k → Mat d) (t : Fin k → Bool) :
    (GK c B t)ᴴ = GK c⁻¹ (fun l => (B (c⁻¹ l))ᴴ) t := by
  ext x y
  simp only [Matrix.conjTranspose_apply, GK]
  by_cases h : (fun i => (x i).1) = (fun i => (y i).1)
  · rw [if_pos h.symm, if_pos h]
    have hl : ∀ i, (y i).1 = (x i).1 := fun i => (congrFun h i).symm
    rw [star_mul', star_prod, star_prod]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hl i]; split_ifs <;> simp
    · rw [← Equiv.prod_comp c (fun i => star (B (c⁻¹ i) (y i).2 (x (c⁻¹ i)).2))]
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]


/-- labelled kernel with coordinate part `V` and sign pattern `t` -/
def LK {d k : ℕ} (V : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) (t : Fin k → Bool) :
    Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ :=
  fun x y => if (fun i => (x i).1) = (fun i => (y i).1) then
    (∏ i, if t i && (x i).1 then (-1 : ℂ) else 1) * V (fun i => (x i).2) (fun i => (y i).2) else 0

/-- coordinate part of a permutation kernel -/
def PK {d k : ℕ} (c : Equiv.Perm (Fin k)) (B : Fin k → Mat d) : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  Matrix.of fun u v => ∏ i, B i (u (c i)) (v i)

lemma GK_eq_LK {d k : ℕ} (c : Equiv.Perm (Fin k)) (B : Fin k → Mat d) (t : Fin k → Bool) :
    GK c B t = LK (PK c B) t := rfl

lemma LK_mul {d k : ℕ} (V V' : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) (t t' : Fin k → Bool) :
    LK V t * LK V' t' = LK (V * V') (fun i => xor (t i) (t' i)) := by
  ext x y
  simp only [Matrix.mul_apply, LK]
  rw [sum_split]
  by_cases h : (fun i => (x i).1) = (fun i => (y i).1)
  · rw [if_pos h]
    rw [Finset.sum_eq_single (fun i => (x i).1)]
    · simp only [if_true, h]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      have hs : (∏ i, (if t i && (x i).1 then (-1 : ℂ) else 1)) * (∏ i, (if t' i && (x i).1 then (-1 : ℂ) else 1)) =
          ∏ i, (if xor (t i) (t' i) && (x i).1 then (-1 : ℂ) else 1) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        cases t i <;> cases t' i <;> cases (x i).1 <;> simp
      rw [← hs]; ring
    · intro b _ hb
      refine Finset.sum_eq_zero (fun z _ => ?_)
      rw [if_neg (fun h' => hb (by funext i; exact (congrFun h' i).symm)), zero_mul]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun z _ => ?_))
    by_cases h1 : (fun i => (x i).1) = b
    · rw [if_neg (fun h2 => h (h1.trans h2)), mul_zero]
    · rw [if_neg h1, zero_mul]

lemma label_sum_LK {d k : ℕ} (P N : Fin k → Mat d) (V : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
    (t : Fin k → Bool) :
    (tensor k (fun i => Xl (P i) (N i)) * LK V t).trace =
      (tensor k (fun i => if t i then N i else P i) * V).trace := by
  rw [tr2, tr2]
  simp only [LK]
  rw [sum_split]
  simp only [sum_split (fun y => _ * _)]
  have hP : ∀ (b b' : Fin k → Bool) (z z' : Fin k → Fin d),
      tensor k (fun i => Xl (P i) (N i)) (fun i => (b i, z i)) (fun i => (b' i, z' i)) =
        ∏ i, Xl (P i) (N i) (b i, z i) (b' i, z' i) := by
    intro b b' z z'; rfl
  simp only [hP]
  have hkill : ∀ (b : Fin k → Bool) (z : Fin k → Fin d),
      ∑ b' : Fin k → Bool, ∑ z' : Fin k → Fin d, (∏ i, Xl (P i) (N i) (b i, z i) (b' i, z' i)) *
        (if (fun i => b' i) = (fun i => b i) then
          (∏ i, if t i && b' i then (-1 : ℂ) else 1) * V z' z else 0) =
      ∑ z' : Fin k → Fin d, (∏ i, (if t i && b i then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if b i then (P i - N i) else (P i + N i)) (z i) (z' i))) * V z' z := by
    intro b z
    rw [Finset.sum_eq_single b]
    · refine Finset.sum_congr rfl (fun z' _ => ?_)
      simp only [if_true, Xl, Finset.prod_mul_distrib]
      ring
    · intro b' _ hb'
      refine Finset.sum_eq_zero (fun z' _ => ?_)
      rw [if_neg (fun h => hb' h), mul_zero]
    · simp
  simp only [hkill]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z' _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun i c => (if t i && c then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if c then (P i - N i) else (P i + N i)) (z i) (z' i)))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Fintype.sum_bool, Bool.and_true, Bool.and_false, if_true, Bool.false_eq_true, if_false]
  by_cases hti : t i
  · rw [if_pos hti, if_pos hti]
    simp only [Matrix.sub_apply, Matrix.add_apply]; ring
  · rw [if_neg hti, if_neg hti]
    simp only [Matrix.sub_apply, Matrix.add_apply]; ring



lemma cross_term {d k : ℕ} (ρ σ : Mat d) (c c' : Equiv.Perm (Fin k)) (B B' : Fin k → Mat d)
    (t t' : Fin k → Bool) :
    weightedInner (labelledState ρ σ) k (GK c B t) (GK c' B' t') =
      ∑ w : Fin k → Fin d, ∏ i, (B' i * (if t i = t' i then plus ρ σ else minus ρ σ) * (B i)ᴴ)
        (w (c' i)) (w (c i)) := by
  unfold weightedInner
  rw [GK_adj, GK_eq_LK, GK_eq_LK, Matrix.mul_assoc, LK_mul, ← Xl_labelled]
  rw [show powerState (Xl (plus ρ σ) (minus ρ σ)) k = tensor k (fun _ => Xl (plus ρ σ) (minus ρ σ)) from rfl]
  rw [label_sum_LK (fun _ => plus ρ σ) (fun _ => minus ρ σ)]
  set Y : Fin k → Mat d := fun i => if t i = t' i then plus ρ σ else minus ρ σ with hY
  have hYeq : (fun i => if xor (t i) (t' i) then minus ρ σ else plus ρ σ) = Y := by
    funext i; simp only [hY]; cases t i <;> cases t' i <;> simp
  rw [hYeq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensor, OptimalSpectrum.Entangled.kronFamily,
    Matrix.of_apply, PK]
  have hV : ∀ v w : Fin k → Fin d, (∏ l, (B (c⁻¹ l))ᴴ (v (c⁻¹ l)) (w l)) = ∏ i, (B i)ᴴ (v i) (w (c i)) := by
    intro v w
    rw [← Equiv.prod_comp c (fun l => (B (c⁻¹ l))ᴴ (v (c⁻¹ l)) (w l))]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  simp only [hV]
  -- reorder: Σ_u Σ_v Σ_w → Σ_w Σ_u Σ_v
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, v]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hcomb : ∀ u v : Fin k → Fin d, (∏ i, Y i (u i) (v i)) * ((∏ i, (B i)ᴴ (v i) (w (c i))) *
      ∏ i, B' i (w (c' i)) (u i)) = ∏ i, (B' i (w (c' i)) (u i) * Y i (u i) (v i) * (B i)ᴴ (v i) (w (c i))) := by
    intro u v
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => by ring)
  simp only [hcomb]
  have h1 : ∀ v : Fin k → Fin d, ∑ u : Fin k → Fin d,
      ∏ i, (B' i (w (c' i)) (u i) * Y i (u i) (v i) * (B i)ᴴ (v i) (w (c i))) =
      ∏ i, ∑ a, (B' i (w (c' i)) a * Y i a (v i) * (B i)ᴴ (v i) (w (c i))) := fun v =>
    (Fintype.prod_sum (fun i a => B' i (w (c' i)) a * Y i a (v i) * (B i)ᴴ (v i) (w (c i)))).symm
  simp only [h1]
  rw [← Fintype.prod_sum (fun i b => ∑ a, (B' i (w (c' i)) a * Y i a b * (B i)ᴴ b (w (c i))))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Finset.sum_mul]
  rfl


section Tsec
open Equiv
def T {ι : Type*} [Fintype ι] (n : ℕ) (M : Fin n → Matrix ι ι ℂ) (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∑ x : Fin n → ι, ∏ i, M (σ i) (x (σ i)) (x i)

lemma sum_cons {ι : Type*} [Fintype ι] {n : ℕ} (f : (Fin (n+1) → ι) → ℂ) :
    ∑ x, f x = ∑ x0 : ι, ∑ x' : Fin n → ι, f (Fin.cons x0 x') := by
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma T_zero {ι : Type*} [Fintype ι] {n : ℕ} (M : Fin (n+1) → Matrix ι ι ℂ) (e : Equiv.Perm (Fin n)) :
    T (n+1) M (Equiv.Perm.decomposeFin.symm (0, e)) = (M 0).trace * T n (fun i => M i.succ) e := by
  unfold T
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [Finset.mul_sum]
  rfl

lemma T_succ {ι : Type*} [Fintype ι] {n : ℕ} (M : Fin (n+1) → Matrix ι ι ℂ) (e : Equiv.Perm (Fin n))
    (q : Fin n) :
    T (n+1) M (Equiv.Perm.decomposeFin.symm (q.succ, e)) =
      T n (fun i => if i = q then M i.succ * M 0 else M i.succ) e := by
  unfold T
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cons_zero]
  set y0 := e.symm q with hy0
  have hswap : ∀ y : Fin n, swap 0 q.succ (e y).succ = if e y = q then 0 else (e y).succ := by
    intro y
    by_cases h : e y = q
    · rw [if_pos h, h, Equiv.swap_apply_right]
    · rw [if_neg h, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h' => h (Fin.succ_injective _ h'))]
  simp only [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  -- split off y0 on both sides
  have hsplit : ∀ (F : Fin n → ℂ), ∏ y, F y = F y0 * ∏ y ∈ Finset.univ.erase y0, F y := fun F =>
    (Finset.mul_prod_erase _ _ (Finset.mem_univ y0)).symm
  have hey0 : e y0 = q := by rw [hy0]; simp
  have hrest : ∀ x0 : ι, ∏ y ∈ Finset.univ.erase y0,
      M (if e y = q then 0 else (e y).succ) ((Fin.cons x0 x' : Fin (n+1) → ι) (if e y = q then 0 else (e y).succ))
        (x' y) =
      ∏ y ∈ Finset.univ.erase y0,
        (if e y = q then M (e y).succ * M 0 else M (e y).succ) (x' (e y)) (x' y) := by
    intro x0
    refine Finset.prod_congr rfl (fun y hy => ?_)
    have hne : e y ≠ q := by
      intro h; apply Finset.ne_of_mem_erase hy; rw [hy0, ← h]; simp
    simp only [if_neg hne, Fin.cons_succ]
  simp only [hsplit, hey0, if_true, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [hrest x0]; ring

def dcyc : (n : ℕ) → Equiv.Perm (Fin n) → ℕ
  | 0, _ => 0
  | n+1, σ => dcyc n (Equiv.Perm.decomposeFin σ).2 + if (Equiv.Perm.decomposeFin σ).1 = 0 then 0 else 1

lemma dcyc_symm {n : ℕ} (p : Fin (n+1)) (e : Equiv.Perm (Fin n)) :
    dcyc (n+1) (Equiv.Perm.decomposeFin.symm (p, e)) = dcyc n e + if p = 0 then 0 else 1 := by
  simp [dcyc]

lemma sum_dcyc (β : ℝ) : ∀ n : ℕ, ∑ σ : Equiv.Perm (Fin n), β^(dcyc n σ) =
    ∏ l ∈ Finset.range n, (1 + (l:ℝ)*β)
  | 0 => by simp [dcyc]
  | n+1 => by
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
    simp only [dcyc_symm, pow_add]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_dcyc β n, Finset.prod_range_succ]
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [if_true, pow_zero, Fin.succ_ne_zero, if_false, pow_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma T_nil {ι : Type*} [Fintype ι] (M : Fin 0 → Matrix ι ι ℂ) (σ : Equiv.Perm (Fin 0)) : T 0 M σ = 1 := by
  simp [T]


lemma cross_T {d k : ℕ} (ρ σ : Mat d) (c c' : Equiv.Perm (Fin k)) (B B' : Fin k → Mat d)
    (t t' : Fin k → Bool) :
    weightedInner (labelledState ρ σ) k (GK c B t) (GK c' B' t') =
      T k (fun l => B' (c'⁻¹ l) * (if t (c'⁻¹ l) = t' (c'⁻¹ l) then plus ρ σ else minus ρ σ) *
        (B (c'⁻¹ l))ᴴ) (c' * c⁻¹) := by
  rw [cross_term]
  unfold T
  refine Finset.sum_congr rfl (fun w _ => ?_)
  symm
  rw [← Equiv.prod_comp c]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

end Tsec

section normsec
variable {d : ℕ}

lemma sum_normsq' (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


lemma inner_eq (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma opNorm_le_of_quad {A : Mat d} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin d → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ c * (star x ⬝ᵥ x).re) :
    opNorm A ≤ c := by
  unfold opNorm
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℂ) A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le (fun x => ?_)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  rw [inner_eq, normsq_eq]
  rcases eq_or_lt_of_le (sq_nonneg ‖x‖) with h0 | hpos
  · rw [normsq_eq] at h0; rw [← h0]; simp [hc]
  · rw [normsq_eq] at hpos
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h _

lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq, normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq']; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq'] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this



lemma opNorm_nonneg' (A : Mat d) : 0 ≤ opNorm A := norm_nonneg _

lemma opNorm_mul_le (A B : Mat d) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact norm_mul_le _ _

lemma opNorm_conj (A : Mat d) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

lemma quad_dot_le (W : Mat d) (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) :
    ‖star (WithLp.ofLp v) ⬝ᵥ (W *ᵥ WithLp.ofLp v)‖ ≤ opNorm W := by
  have h1 : star (WithLp.ofLp v) ⬝ᵥ (W *ᵥ WithLp.ofLp v) = inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) W v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]
  rw [h1]
  calc ‖inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) W v)‖ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) W v‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) W‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = opNorm W := by rw [hv]; unfold opNorm; ring

lemma re_nonneg_of_psd {A : Mat d} (hA : A.PosSemidef) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

/-- sandwich: |quad Y| ≤ quad X -/

lemma trace_pure_mul (v : EuclideanSpace ℂ (Fin d)) (W : Mat d) :
    (QAlgorithms.pureDensity v * W).trace = star (WithLp.ofLp v) ⬝ᵥ (W *ᵥ WithLp.ofLp v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp only [RCLike.star_def]; ring

lemma spectral_sum {X : Mat d} (hX : X.IsHermitian) :
    X = ∑ i, ((hX.eigenvalues i : ℝ) : ℂ) • QAlgorithms.pureDensity (hX.eigenvectorBasis i) := by
  conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, QAlgorithms.pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, smul_eq_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.star_apply]
  simp only [RCLike.star_def]; rw [mul_right_comm, mul_comm]; exact rfl

lemma trace_onb (S : Mat d) {X : Mat d} (hX : X.IsHermitian) :
    S.trace = ∑ i, star (WithLp.ofLp (hX.eigenvectorBasis i)) ⬝ᵥ (S *ᵥ WithLp.ofLp (hX.eigenvectorBasis i)) := by
  set U := (hX.eigenvectorUnitary : Mat d)
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  have : S.trace = (star U * S * U).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [this]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
    Matrix.star_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

lemma trace_sandwich_le {X S : Mat d} (hX : X.IsHermitian) (hlo : (S + X).PosSemidef)
    (hhi : (S - X).PosSemidef) (W : Mat d) :
    ‖(X * W).trace‖ ≤ (S.trace).re * opNorm W := by
  set v := hX.eigenvectorBasis
  set lam := hX.eigenvalues
  have hv1 : ∀ i, ‖v i‖ = 1 := fun i => hX.eigenvectorBasis.orthonormal.1 i
  have hvv : ∀ i, star (WithLp.ofLp (v i)) ⬝ᵥ WithLp.ofLp (v i) = 1 := by
    intro i
    have := normsq_eq (v i); rw [hv1 i, one_pow] at this
    rw [sum_normsq']
    rw [sum_normsq'] at this
    simp only [Complex.re_sum, Complex.ofReal_re] at this
    rw [← Complex.ofReal_sum, ← this]; simp
  have hXv : ∀ i, X *ᵥ WithLp.ofLp (v i) = lam i • WithLp.ofLp (v i) := fun i => hX.mulVec_eigenvectorBasis i
  have hlam : ∀ i, |lam i| ≤ (star (WithLp.ofLp (v i)) ⬝ᵥ (S *ᵥ WithLp.ofLp (v i))).re := by
    intro i
    have h1 := re_nonneg_of_psd hlo (WithLp.ofLp (v i))
    have h2 := re_nonneg_of_psd hhi (WithLp.ofLp (v i))
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hXv, dotProduct_smul, hvv] at h1
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hXv, dotProduct_smul, hvv] at h2
    simp only [Complex.real_smul, mul_one, Complex.ofReal_re] at h1 h2
    rw [abs_le]; constructor <;> linarith
  rw [spectral_sum hX, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_pure_mul]
  calc ‖∑ i, ((lam i : ℝ) : ℂ) * (star (WithLp.ofLp (v i)) ⬝ᵥ (W *ᵥ WithLp.ofLp (v i)))‖
      ≤ ∑ i, ‖((lam i : ℝ) : ℂ) * (star (WithLp.ofLp (v i)) ⬝ᵥ (W *ᵥ WithLp.ofLp (v i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, (star (WithLp.ofLp (v i)) ⬝ᵥ (S *ᵥ WithLp.ofLp (v i))).re * opNorm W := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hlam i) (quad_dot_le W (v i) (hv1 i)) (norm_nonneg _)
          (le_trans (abs_nonneg _) (hlam i))
    _ = (S.trace).re * opNorm W := by
        rw [← Finset.sum_mul, trace_onb S hX, Complex.re_sum]


end normsec

section goodsec
variable {d : ℕ}

/-- admissible middle factors: sandwiched by `S` -/
def Adm (S X : Mat d) : Prop := X.IsHermitian ∧ (S + X).PosSemidef ∧ (S - X).PosSemidef

def gprod (l : List (Mat d × Mat d × Mat d)) : Mat d := (l.map (fun p => p.1 * p.2.1 * p.2.2)).prod
def gweight (l : List (Mat d × Mat d × Mat d)) : ℝ := (l.map (fun p => opNorm p.1 * opNorm p.2.2)).prod

lemma gprod_append (l l' : List (Mat d × Mat d × Mat d)) : gprod (l ++ l') = gprod l * gprod l' := by
  simp [gprod, List.map_append, List.prod_append]

lemma gweight_append (l l' : List (Mat d × Mat d × Mat d)) : gweight (l ++ l') = gweight l * gweight l' := by
  simp [gweight, List.map_append, List.prod_append]

lemma gweight_nonneg (l : List (Mat d × Mat d × Mat d)) : 0 ≤ gweight l := by
  unfold gweight
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_nonneg (mul_nonneg (opNorm_nonneg' _) (opNorm_nonneg' _)) ih

lemma opNorm_one_le : opNorm (1 : Mat d) ≤ 1 := by
  unfold opNorm; rw [map_one]; exact ContinuousLinearMap.norm_id_le

lemma opNorm_list_le (l : List (Mat d)) : opNorm l.prod ≤ (l.map opNorm).prod := by
  induction l with
  | nil => simpa using opNorm_one_le
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons]
    exact (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (opNorm_nonneg' _))

lemma adm_opNorm {S X : Mat d} (hS : S.PosSemidef) (hX : Adm S X) : opNorm X ≤ opNorm S := by
  refine opNorm_le_of_quad hX.1 (opNorm_nonneg' S) (fun x => ?_)
  have h1 := re_nonneg_of_psd hX.2.1 x
  have h2 := re_nonneg_of_psd hX.2.2 x
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re] at h1
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h2
  have h3 := quad_le_opNorm S x
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

lemma good_trace {S : Mat d} (hS : S.PosSemidef) (htr : (S.trace).re ≤ 1) {β : ℝ} (hβ : opNorm S ≤ β)
    (p : Mat d × Mat d × Mat d) (l : List (Mat d × Mat d × Mat d))
    (hadm : ∀ q ∈ p :: l, Adm S q.2.1) :
    ‖(gprod (p :: l)).trace‖ ≤ β ^ l.length * gweight (p :: l) := by
  obtain ⟨D, X, E⟩ := p
  have hβ0 : 0 ≤ β := le_trans (opNorm_nonneg' S) hβ
  simp only [gprod, gweight, List.map_cons, List.prod_cons]
  set R := (l.map (fun p => p.1 * p.2.1 * p.2.2)).prod
  have htrace : (D * X * E * R).trace = (X * (E * R * D)).trace := by
    rw [show D * X * E * R = D * (X * E * R) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm D]
    simp only [Matrix.mul_assoc]
  rw [htrace]
  have hXadm := hadm (D, X, E) List.mem_cons_self
  have h1 := trace_sandwich_le hXadm.1 hXadm.2.1 hXadm.2.2 (E * R * D)
  have hR : opNorm R ≤ β ^ l.length * (l.map (fun p => opNorm p.1 * opNorm p.2.2)).prod := by
    refine (opNorm_list_le _).trans ?_
    rw [List.map_map]
    have : ∀ (l' : List (Mat d × Mat d × Mat d)), (∀ q ∈ l', Adm S q.2.1) →
        (l'.map ((fun A => opNorm A) ∘ (fun p => p.1 * p.2.1 * p.2.2))).prod ≤
          β ^ l'.length * (l'.map (fun p => opNorm p.1 * opNorm p.2.2)).prod := by
      intro l' hl'
      induction l' with
      | nil => simp
      | cons q l' ih =>
        simp only [List.map_cons, List.prod_cons, List.length_cons, Function.comp_apply, pow_succ]
        have hq := hl' q List.mem_cons_self
        have hX : opNorm q.2.1 ≤ β := (adm_opNorm hS hq).trans hβ
        have hih := ih (fun r hr => hl' r (List.mem_cons_of_mem q hr))
        have hm : opNorm (q.1 * q.2.1 * q.2.2) ≤ β * (opNorm q.1 * opNorm q.2.2) := by
          calc opNorm (q.1 * q.2.1 * q.2.2) ≤ opNorm q.1 * opNorm q.2.1 * opNorm q.2.2 :=
                (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg' _))
            _ ≤ opNorm q.1 * β * opNorm q.2.2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (opNorm_nonneg' _)) (opNorm_nonneg' _)
            _ = β * (opNorm q.1 * opNorm q.2.2) := by ring
        have hw : 0 ≤ (l'.map ((fun A => opNorm A) ∘ (fun p => p.1 * p.2.1 * p.2.2))).prod :=
          List.prod_nonneg (fun a ha => by
            obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact opNorm_nonneg' _)
        calc opNorm (q.1 * q.2.1 * q.2.2) * (l'.map ((fun A => opNorm A) ∘ (fun p => p.1 * p.2.1 * p.2.2))).prod
            ≤ (β * (opNorm q.1 * opNorm q.2.2)) * (β ^ l'.length * (l'.map (fun p => opNorm p.1 * opNorm p.2.2)).prod) :=
              mul_le_mul hm hih hw (mul_nonneg hβ0 (mul_nonneg (opNorm_nonneg' _) (opNorm_nonneg' _)))
          _ = _ := by ring
    exact this l (fun q hq => hadm q (List.mem_cons_of_mem _ hq))
  have hERD : opNorm (E * R * D) ≤ opNorm E * opNorm R * opNorm D :=
    (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg' _))
  have htr0 : 0 ≤ (S.trace).re := by
    have := hS.trace_nonneg; exact (Complex.nonneg_iff.1 this).1
  calc ‖(X * (E * R * D)).trace‖ ≤ (S.trace).re * opNorm (E * R * D) := h1
    _ ≤ 1 * (opNorm E * opNorm R * opNorm D) :=
        mul_le_mul htr hERD (opNorm_nonneg' _) zero_le_one
    _ ≤ 1 * (opNorm E * (β ^ l.length * (l.map (fun p => opNorm p.1 * opNorm p.2.2)).prod) * opNorm D) := by
        gcongr
        · exact opNorm_nonneg' _
        · exact opNorm_nonneg' _
    _ = β ^ l.length * ((opNorm D * opNorm E) * (l.map (fun p => opNorm p.1 * opNorm p.2.2)).prod) := by ring

lemma T_good {S : Mat d} (hS : S.PosSemidef) (htr : (S.trace).re ≤ 1) {β : ℝ} (hβ0 : 0 < β)
    (hβ : opNorm S ≤ β) :
    ∀ (n : ℕ) (ls : Fin n → List (Mat d × Mat d × Mat d)), (∀ i, ls i ≠ []) →
      (∀ i, ∀ q ∈ ls i, Adm S q.2.1) → ∀ σ : Equiv.Perm (Fin n),
      ‖T n (fun i => gprod (ls i)) σ‖ ≤
        (∏ i, gweight (ls i)) * β ^ ((∑ i, ((ls i).length - 1)) + dcyc n σ)
  | 0, ls, _, _, σ => by simp [T_nil, dcyc]
  | n+1, ls, hne, hadm, σ => by
    obtain ⟨⟨p, e⟩, rfl⟩ : ∃ pe, Equiv.Perm.decomposeFin.symm pe = σ :=
      ⟨Equiv.Perm.decomposeFin σ, by simp⟩
    rw [dcyc_symm]
    refine Fin.cases ?_ (fun q => ?_) p
    · rw [T_zero]
      obtain ⟨p0, l0, hl0⟩ : ∃ p0 l0, ls 0 = p0 :: l0 := by
        cases h : ls 0 with
        | nil => exact absurd h (hne 0)
        | cons a l => exact ⟨a, l, rfl⟩
      have h1 := good_trace hS htr hβ p0 l0 (by rw [← hl0]; exact hadm 0)
      rw [← hl0] at h1
      have h2 := T_good hS htr hβ0 hβ n (fun i => ls i.succ) (fun i => hne _) (fun i => hadm _) e
      rw [norm_mul]
      have hlen : (ls 0).length - 1 = l0.length := by rw [hl0]; simp
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, if_pos rfl, add_zero, hlen]
      calc ‖(gprod (ls 0)).trace‖ * ‖T n (fun i => gprod (ls i.succ)) e‖
          ≤ (β ^ l0.length * gweight (ls 0)) *
              ((∏ i : Fin n, gweight (ls i.succ)) * β ^ ((∑ i : Fin n, ((ls i.succ).length - 1)) + dcyc n e)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (pow_nonneg hβ0.le _) (gweight_nonneg _))
        _ = _ := by rw [pow_add, pow_add, pow_add]; ring
    · rw [T_succ]
      set ls' : Fin n → List (Mat d × Mat d × Mat d) := fun i => if i = q then ls i.succ ++ ls 0 else ls i.succ
        with hls'
      have hM : (fun i : Fin n => if i = q then gprod (ls i.succ) * gprod (ls 0) else gprod (ls i.succ)) =
          fun i => gprod (ls' i) := by
        funext i; by_cases h : i = q <;> simp [hls', h, gprod_append]
      rw [hM]
      have hne' : ∀ i, ls' i ≠ [] := by
        intro i; by_cases h : i = q <;> simp [hls', h, hne]
      have hadm' : ∀ i, ∀ r ∈ ls' i, Adm S r.2.1 := by
        intro i r hr
        by_cases h : i = q
        · simp only [hls', h, if_true, List.mem_append] at hr
          rcases hr with hr | hr
          · exact hadm _ r hr
          · exact hadm 0 r hr
        · simp only [hls', h, if_false] at hr; exact hadm _ r hr
      have h2 := T_good hS htr hβ0 hβ n ls' hne' hadm' e
      refine h2.trans (le_of_eq ?_)
      have hw : ∏ i, gweight (ls' i) = ∏ i, gweight (ls i) := by
        rw [Fin.prod_univ_succ]
        have : ∀ i, gweight (ls' i) = gweight (ls i.succ) * (if i = q then gweight (ls 0) else 1) := by
          intro i; by_cases h : i = q <;> simp [hls', h, gweight_append]
        simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
        ring
      have hlen : ∑ i, ((ls' i).length - 1) = (∑ i : Fin n, ((ls i.succ).length - 1)) + (ls 0).length := by
        have : ∀ i, (ls' i).length - 1 = ((ls i.succ).length - 1) + (if i = q then (ls 0).length else 0) := by
          intro i
          have h1 : (ls i.succ).length ≥ 1 := List.length_pos_of_ne_nil (hne _)
          by_cases h : i = q
          · subst h; simp only [hls', if_true, List.length_append]; omega
          · simp only [hls', h, if_false]; omega
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hw, hlen, Fin.sum_univ_succ, if_neg (Fin.succ_ne_zero q)]
      have h0 : (ls 0).length ≥ 1 := List.length_pos_of_ne_nil (hne 0)
      congr 2
      omega

end goodsec

lemma cross_bound {d k : ℕ} (ρ σ Q : Mat d) (hQH : Qᴴ = Q) (hQ : Q * Q = Q)
    (hS : (Q * plus ρ σ * Q).PosSemidef)
    (htr : ((Q * plus ρ σ * Q).trace).re ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ : opNorm (Q * plus ρ σ * Q) ≤ β)
    (hmin : Adm (Q * plus ρ σ * Q) (Q * minus ρ σ * Q))
    (c c' : Equiv.Perm (Fin k)) (B B' : Fin k → Mat d) (hB : ∀ i, Q * B i * Q = B i)
    (hB' : ∀ i, Q * B' i * Q = B' i) (t t' : Fin k → Bool) :
    ‖weightedInner (labelledState ρ σ) k (GK c B t) (GK c' B' t')‖ ≤
      (∏ i, opNorm (B i) * opNorm (B' i)) * β ^ (dcyc k (c' * c⁻¹)) := by
  rw [cross_T]
  set S := Q * plus ρ σ * Q with hSdef
  have hB'Q : ∀ i, B' i * Q = B' i := by
    intro i; conv_lhs => rw [← hB' i]
    rw [Matrix.mul_assoc, hQ, hB' i]
  have hQB : ∀ i, Q * (B i)ᴴ = (B i)ᴴ := by
    intro i
    have : (B i)ᴴ = Q * (B i)ᴴ * Q := by
      conv_lhs => rw [← hB i]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH]; simp only [Matrix.mul_assoc]
    conv_lhs => rw [this]
    simp only [← Matrix.mul_assoc]
    rw [hQ, ← this]
  set ls : Fin k → List (Mat d × Mat d × Mat d) := fun l =>
    [(B' (c'⁻¹ l), Q * (if t (c'⁻¹ l) = t' (c'⁻¹ l) then plus ρ σ else minus ρ σ) * Q, (B (c'⁻¹ l))ᴴ)] with hls
  have hM : (fun l => B' (c'⁻¹ l) * (if t (c'⁻¹ l) = t' (c'⁻¹ l) then plus ρ σ else minus ρ σ) *
      (B (c'⁻¹ l))ᴴ) = fun l => gprod (ls l) := by
    funext l
    simp only [hls, gprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'Q, Matrix.mul_assoc, Matrix.mul_assoc, hQB,
      ← Matrix.mul_assoc]
  rw [hM]
  have hadmS : Adm S S := ⟨hS.1, hS.add hS, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩
  have h := T_good hS htr hβ0 hβ k ls (fun l => by simp [hls])
    (fun l q hq => by
      simp only [hls, List.mem_singleton] at hq
      subst hq
      by_cases ht : t (c'⁻¹ l) = t' (c'⁻¹ l)
      · simp only [ht, if_true]; exact hadmS
      · simp only [ht, if_false]; exact hmin) (c' * c⁻¹)
  refine h.trans (le_of_eq ?_)
  have hlen : ∑ l, ((ls l).length - 1) = 0 := by simp [hls]
  rw [hlen, zero_add]
  congr 1
  simp only [hls, gweight, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, opNorm_conj]
  rw [← Equiv.prod_comp c'⁻¹ (fun l => opNorm (B l) * opNorm (B' l))]
  refine Finset.prod_congr rfl (fun l _ => by ring)


section fibers

lemma fiber_le {k : ℕ} (c : Equiv.Perm (Fin k)) (x0 : Fin k) (hfull : ∀ x, ∃ n : ℕ, (c ^ n) x0 = x)
    (σ : Equiv.Perm (Fin k)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ)).card ≤ k := by
  by_cases hne : (Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ)).Nonempty
  · obtain ⟨π0, hπ0⟩ := hne
    have hπ0' : π0 * c * π0⁻¹ = σ := (Finset.mem_filter.1 hπ0).2
    have hcomm : ∀ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ),
        (π0⁻¹ * π) * c = c * (π0⁻¹ * π) := by
      intro π hπ
      have h1 : π * c * π⁻¹ = π0 * c * π0⁻¹ := (Finset.mem_filter.1 hπ).2.trans hπ0'.symm
      have : π0⁻¹ * (π * c * π⁻¹) * π = π0⁻¹ * (π0 * c * π0⁻¹) * π := by rw [h1]
      simp only [mul_assoc, inv_mul_cancel, mul_one] at this
      rw [← mul_assoc, ← mul_assoc] at this
      simp only [mul_assoc] at this ⊢
      calc π0⁻¹ * (π * c) = π0⁻¹ * π * c := by rw [mul_assoc]
        _ = c * (π0⁻¹ * π) := by
          have h2 : π0⁻¹ * π * c * π⁻¹ * π0 = c := by
            have := congrArg (fun z => π0⁻¹ * z * π0) h1
            simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at this
            simpa [mul_assoc] using this
          calc π0⁻¹ * π * c = (π0⁻¹ * π * c * π⁻¹ * π0) * (π0⁻¹ * π) := by group
            _ = c * (π0⁻¹ * π) := by rw [h2]
    have hpow : ∀ (ρ : Equiv.Perm (Fin k)), ρ * c = c * ρ → ∀ n : ℕ, ρ ((c ^ n) x0) = (c ^ n) (ρ x0) := by
      intro ρ hρ n
      have : ρ * c ^ n = c ^ n * ρ := (Commute.pow_right hρ n)
      exact congrArg (fun f : Equiv.Perm (Fin k) => f x0) this
    calc (Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ)).card
        ≤ (Finset.univ : Finset (Fin k)).card := by
          refine Finset.card_le_card_of_injOn (fun π => (π0⁻¹ * π) x0) (fun _ _ => Finset.mem_univ _) ?_
          intro π1 h1 π2 h2 heq
          simp only at heq
          have hρ : π0⁻¹ * π1 = π0⁻¹ * π2 := by
            ext x
            obtain ⟨n, rfl⟩ := hfull x
            rw [hpow _ (hcomm π1 h1) n, hpow _ (hcomm π2 h2) n, heq]
          exact mul_left_cancel hρ
      _ = k := by simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp

lemma sum_conj_le {k : ℕ} (c : Equiv.Perm (Fin k)) (x0 : Fin k) (hfull : ∀ x, ∃ n : ℕ, (c ^ n) x0 = x)
    (f : Equiv.Perm (Fin k) → ℝ) (hf : ∀ σ, 0 ≤ f σ) :
    ∑ π : Equiv.Perm (Fin k), f (π * c * π⁻¹) ≤ k * ∑ σ, f σ := by
  rw [← Finset.sum_fiberwise Finset.univ (fun π => π * c * π⁻¹) (fun π => f (π * c * π⁻¹))]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun σ _ => ?_)
  have : ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ), f (π * c * π⁻¹) =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) => π * c * π⁻¹ = σ)).card * f σ := by
    rw [Finset.sum_congr rfl (fun π hπ => by rw [(Finset.mem_filter.1 hπ).2]), Finset.sum_const, nsmul_eq_mul]
  rw [this]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_le c x0 hfull σ) (hf σ)

lemma full_rot (m : ℕ) : ∀ x : Fin (m+1), ∃ n : ℕ, (finRotate (m+1) ^ n) 0 = x := by
  have h : ∀ n : ℕ, ∀ hn : n < m + 1, (finRotate (m+1) ^ n) 0 = ⟨n, hn⟩ := by
    intro n; induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), finRotate_apply]
      ext; simp [Fin.val_add]; omega
  intro x; exact ⟨x.val, h x.val x.isLt⟩

lemma full_inv {k : ℕ} (c : Equiv.Perm (Fin k)) (x0 : Fin k) (hfull : ∀ x, ∃ n : ℕ, (c ^ n) x0 = x) :
    ∀ x, ∃ n : ℕ, (c⁻¹ ^ n) x0 = x := by
  set N := Fintype.card (Equiv.Perm (Fin k))
  have hN : 1 ≤ N := Fintype.card_pos
  have hcN : c⁻¹ ^ N = 1 := pow_card_eq_one
  have hc : c⁻¹ ^ (N - 1) = c := by
    have : c⁻¹ ^ (N - 1) * c⁻¹ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN, hcN]
    calc c⁻¹ ^ (N - 1) = c⁻¹ ^ (N - 1) * c⁻¹ * c := by group
      _ = c := by rw [this, one_mul]
  intro x
  obtain ⟨n, hn⟩ := hfull x
  exact ⟨(N - 1) * n, by rw [pow_mul, hc, hn]⟩

end fibers


section wsec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma wI_smul_right (τ : Matrix ι ι ℂ) {k : ℕ} (X Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) (c : ℂ) :
    weightedInner τ k X (c • Y) = c * weightedInner τ k X Y := by
  unfold weightedInner; rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma wI_smul_left (τ : Matrix ι ι ℂ) {k : ℕ} (X Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) (c : ℂ) :
    weightedInner τ k (c • X) Y = star c * weightedInner τ k X Y := by
  unfold weightedInner
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

lemma wI_sum_right (τ : Matrix ι ι ℂ) {k : ℕ} {S : Type*} [Fintype S] (X : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (Y : S → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k X (∑ s, Y s) = ∑ s, weightedInner τ k X (Y s) := by
  unfold weightedInner; rw [Matrix.mul_sum, Matrix.trace_sum]

lemma wI_sum_left (τ : Matrix ι ι ℂ) {k : ℕ} {S : Type*} [Fintype S] (X : S → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k (∑ s, X s) Y = ∑ s, weightedInner τ k (X s) Y := by
  unfold weightedInner
  rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]

end wsec

lemma sym_norm {d k : ℕ} (hk : 1 ≤ k) (ρ σ Q : Mat d) (hQH : Qᴴ = Q) (hQ : Q * Q = Q)
    (hS : (Q * plus ρ σ * Q).PosSemidef)
    (htr : ((Q * plus ρ σ * Q).trace).re ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ : opNorm (Q * plus ρ σ * Q) ≤ β)
    (hmin : Adm (Q * plus ρ σ * Q) (Q * minus ρ σ * Q))
    (c : Equiv.Perm (Fin k)) (x0 : Fin k) (hfull : ∀ x, ∃ n : ℕ, (c ^ n) x0 = x)
    (B : Fin k → Mat d) (hB : ∀ i, Q * B i * Q = B i) (t : Fin k → Bool) :
    weightedNormSq (labelledState ρ σ) k (symmetrize (GK c B t)) ≤
      (∏ i, opNorm (B i)) ^ 2 * cycleFactor β k := by
  set L := labelledState ρ σ
  set P := ∏ i, opNorm (B i) with hP
  set a : ℝ := ((k.factorial : ℝ))⁻¹ with ha
  set X : Equiv.Perm (Fin k) → Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ :=
    fun π => GK (π * c * π⁻¹) (fun l => B (π⁻¹ l)) (fun l => t (π⁻¹ l)) with hX
  have hsymm : symmetrize (GK c B t) = (a : ℂ) • ∑ π, X π := by
    unfold symmetrize
    simp only [GK_conj, hX, ha]; push_cast; rfl
  have hBπ : ∀ π : Equiv.Perm (Fin k), ∀ i, Q * B (π⁻¹ i) * Q = B (π⁻¹ i) := fun π i => hB _
  have hPπ : ∀ π π' : Equiv.Perm (Fin k), (∏ i, opNorm (B (π⁻¹ i)) * opNorm (B (π'⁻¹ i))) = P ^ 2 := by
    intro π π'
    rw [Finset.prod_mul_distrib, sq, Equiv.prod_comp π⁻¹ (fun i => opNorm (B i)),
      Equiv.prod_comp π'⁻¹ (fun i => opNorm (B i))]
  have hcross : ∀ π π' : Equiv.Perm (Fin k), ‖weightedInner L k (X π) (X π')‖ ≤
      P ^ 2 * β ^ (dcyc k ((π' * c * π'⁻¹) * (π * c * π⁻¹)⁻¹)) := by
    intro π π'
    have := cross_bound ρ σ Q hQH hQ hS htr hβ0 hβ hmin (π * c * π⁻¹) (π' * c * π'⁻¹)
      (fun l => B (π⁻¹ l)) (fun l => B (π'⁻¹ l)) (hBπ π) (hBπ π') (fun l => t (π⁻¹ l)) (fun l => t (π'⁻¹ l))
    rwa [hPπ] at this
  have hinner : ∀ π : Equiv.Perm (Fin k), ∑ π' : Equiv.Perm (Fin k),
      β ^ (dcyc k ((π' * c * π'⁻¹) * (π * c * π⁻¹)⁻¹)) ≤ k * ∏ l ∈ Finset.range k, (1 + (l:ℝ) * β) := by
    intro π
    have h1 := sum_conj_le c x0 hfull (fun σ' => β ^ (dcyc k (σ' * (π * c * π⁻¹)⁻¹)))
      (fun _ => pow_nonneg hβ0.le _)
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [← sum_dcyc β k]
    exact Equiv.sum_comp (Equiv.mulRight (π * c * π⁻¹)⁻¹) (fun σ' => β ^ (dcyc k σ'))
  unfold weightedNormSq
  rw [hsymm, wI_smul_left, wI_smul_right, wI_sum_left]
  simp only [wI_sum_right]
  have hstar : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  rw [hstar, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have ha0 : 0 ≤ a * a := mul_self_nonneg a
  calc a * a * (∑ π, ∑ π', weightedInner L k (X π) (X π')).re
      ≤ a * a * ‖∑ π, ∑ π', weightedInner L k (X π) (X π')‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) ha0
    _ ≤ a * a * (∑ π : Equiv.Perm (Fin k), ∑ π' : Equiv.Perm (Fin k),
          P ^ 2 * β ^ (dcyc k ((π' * c * π'⁻¹) * (π * c * π⁻¹)⁻¹))) := by
        refine mul_le_mul_of_nonneg_left ?_ ha0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun π _ => ?_))
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun π' _ => hcross π π'))
    _ ≤ a * a * (∑ _π : Equiv.Perm (Fin k), P ^ 2 * (k * ∏ l ∈ Finset.range k, (1 + (l:ℝ) * β))) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => ?_)) ha0
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hinner π) (sq_nonneg _)
    _ = P ^ 2 * cycleFactor β k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        unfold cycleFactor
        rw [ha]
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [Nat.factorial_succ, Nat.add_sub_cancel]
        push_cast
        field_simp
        simp only [mul_comm (β)]


section seminorm
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- vectorization twisted by a square root factor -/
def tw (Bh : Matrix κ κ ℂ) (V : Matrix κ κ ℂ) : EuclideanSpace ℂ (κ × κ) :=
  WithLp.toLp 2 (fun p => (V * Bh) p.1 p.2)

lemma tw_add (Bh V W : Matrix κ κ ℂ) : tw Bh (V + W) = tw Bh V + tw Bh W := by
  unfold tw; rw [Matrix.add_mul]; rfl

lemma tw_smul (Bh V : Matrix κ κ ℂ) (c : ℂ) : tw Bh (c • V) = c • tw Bh V := by
  unfold tw; rw [Matrix.smul_mul]; rfl

lemma tw_sum {S : Type*} (s : Finset S) (Bh : Matrix κ κ ℂ) (V : S → Matrix κ κ ℂ) :
    tw Bh (∑ a ∈ s, V a) = ∑ a ∈ s, tw Bh (V a) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold tw; simp; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tw_add, ih]

lemma wns_eq_tw {T : Matrix κ κ ℂ} (B : Matrix κ κ ℂ) (hT : T = Bᴴ * B) (V : Matrix κ κ ℂ) :
    (T * Vᴴ * V).trace.re = ‖tw Bᴴ V‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [hT]
  have : (Bᴴ * B * Vᴴ * V).trace = ((V * Bᴴ)ᴴ * (V * Bᴴ)).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Bᴴ * B * Vᴴ * V = Bᴴ * (B * Vᴴ * V) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [this]
  simp only [tw, dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Pi.star_apply, Fintype.sum_prod_type, WithLp.ofLp_toLp, RCLike.re_to_complex]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

end seminorm


section finalsec
open scoped MatrixOrder

lemma kron_conj {ι : Type*} [Fintype ι] {r : ℕ} (A : Fin r → Matrix ι ι ℂ) :
    (OptimalSpectrum.Entangled.kronFamily A)ᴴ =
      OptimalSpectrum.Entangled.kronFamily (fun j => (A j)ᴴ) := by
  ext x y
  simp [OptimalSpectrum.Entangled.kronFamily, conjTranspose_apply, star_prod]

lemma powerState_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ} (hτ : τ.PosSemidef)
    (n : ℕ) : (powerState τ n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  have : powerState τ n = (OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B))ᴴ *
      OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B) := by
    rw [kron_conj, ← kron_mul]
    simp only [powerState, tensor, hB, Matrix.star_eq_conjTranspose]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

lemma labelled_psd {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext ⟨b, i⟩ ⟨b', j⟩
    simp only [labelledState, conjTranspose_apply]
    by_cases h : b' = b
    · subst h
      simp only [if_true]
      cases b'
      · simp only [Bool.false_eq_true, if_false, star_mul', star_inv₀, star_ofNat]
        rw [show star (ρ j i) = ρ i j from by
          have := congrFun (congrFun hρ.1.1 i) j; simpa [conjTranspose_apply] using this]
      · simp only [if_true, star_mul', star_inv₀, star_ofNat]
        rw [show star (σ j i) = σ i j from by
          have := congrFun (congrFun hσ.1.1 i) j; simpa [conjTranspose_apply] using this]
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · set u : Fin d → ℂ := fun i => x (false, i)
    set w : Fin d → ℂ := fun i => x (true, i)
    have e : star x ⬝ᵥ (labelledState ρ σ *ᵥ x) =
        (2:ℂ)⁻¹ * (star u ⬝ᵥ (ρ *ᵥ u)) + (2:ℂ)⁻¹ * (star w ⬝ᵥ (σ *ᵥ w)) := by
      simp only [dotProduct, mulVec, labelledState, Fintype.sum_prod_type, Fintype.sum_bool,
        Pi.star_apply, u, w]
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    rw [e]
    have h2 : (0:ℂ) ≤ (2:ℂ)⁻¹ := by
      rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
    exact add_nonneg (mul_nonneg h2 (hρ.1.dotProduct_mulVec_nonneg u))
      (mul_nonneg h2 (hσ.1.dotProduct_mulVec_nonneg w))



lemma psd_factor {κ : Type*} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix κ κ ℂ, A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, by rw [hB]; rfl⟩

end finalsec

section linsec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma symmetrize_add {k : ℕ} (V W : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    symmetrize (V + W) = symmetrize V + symmetrize W := by
  unfold symmetrize
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1; refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [Matrix.mul_add, Matrix.add_mul]

lemma symmetrize_smul {k : ℕ} (c : ℂ) (V : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    symmetrize (c • V) = c • symmetrize V := by
  unfold symmetrize
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  congr 1; funext π
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

lemma symmetrize_sum {k : ℕ} {S : Type*} [Fintype S] (V : S → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    symmetrize (∑ s, V s) = ∑ s, symmetrize (V s) := by
  classical
  have : ∀ (t : Finset S), symmetrize (∑ s ∈ t, V s) = ∑ s ∈ t, symmetrize (V s) := by
    intro t
    induction t using Finset.induction_on with
    | empty => unfold symmetrize; simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, symmetrize_add, ih]
  exact this Finset.univ

lemma hermPart_sum {k : ℕ} {S : Type*} [Fintype S] (c : S → ℂ) (K : S → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    hermPart (∑ s, c s • K s) = ∑ s, ((c s / 2) • K s + (star (c s) / 2) • (K s)ᴴ) := by
  unfold hermPart
  rw [Matrix.conjTranspose_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.conjTranspose_smul, smul_add, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

end linsec

lemma opNorm_QXQ {d : ℕ} {Q : Mat d} (hQH : Qᴴ = Q) (hQ : Q * Q = Q) (X : Mat d) :
    opNorm (Q * X * Q) ≤ opNorm X := by
  have hQ1 : opNorm Q ≤ 1 := by
    have hQpsd : Q.PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self Q; rwa [hQH, hQ] at this
    have h1Q : (1 - Q).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self (1 - Q)
      have e : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH, Matrix.sub_mul, Matrix.mul_sub,
          Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQ]; abel
      rwa [e] at this
    refine opNorm_le_of_quad hQpsd.1 zero_le_one (fun x => ?_)
    have h1 := re_nonneg_of_psd hQpsd x
    have h2 := re_nonneg_of_psd h1Q x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h2
    rw [abs_of_nonneg h1, one_mul]; linarith
  have hX0 := opNorm_nonneg' X
  have hQ0 := opNorm_nonneg' Q
  calc opNorm (Q * X * Q) ≤ opNorm Q * opNorm X * opNorm Q :=
        (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg' _))
    _ ≤ opNorm X := by nlinarith [mul_le_mul_of_nonneg_right hQ1 hX0]

lemma repF_sandwich {d m : ℕ} {Q : Mat d} (hQ : Q * Q = Q) (A : Fin (m+2) → Mat d) (i : Fin (m+1)) :
    Q * repF Q A i * Q = repF Q A i := by
  unfold repF
  split_ifs <;> simp only [← Matrix.mul_assoc, hQ] <;> simp only [Matrix.mul_assoc, hQ]

lemma repF_norm {d m : ℕ} {Q : Mat d} (hQH : Qᴴ = Q) (hQ : Q * Q = Q) (A : Fin (m+2) → Mat d) :
    ∏ i, opNorm (repF Q A i) ≤ ∏ i, opNorm (A i) := by
  rw [Fin.prod_univ_castSucc (fun i => opNorm (A i)), Fin.prod_univ_succ (fun i => opNorm (repF Q A i)),
    Fin.prod_univ_succ (fun i => opNorm (A (Fin.castSucc i)))]
  have h0 : opNorm (repF Q A 0) ≤ opNorm (A (Fin.last (m+1))) * opNorm (A (Fin.castSucc 0)) := by
    unfold repF; rw [if_pos (by simp)]
    rw [show Q * A (Fin.last (m+1)) * A (Fin.castSucc 0) * Q = Q * (A (Fin.last (m+1)) * A (Fin.castSucc 0)) * Q by
      simp only [Matrix.mul_assoc]]
    exact (opNorm_QXQ hQH hQ _).trans (opNorm_mul_le _ _)
  have hs : ∏ i : Fin m, opNorm (repF Q A i.succ) ≤ ∏ i : Fin m, opNorm (A (Fin.castSucc i.succ)) := by
    refine Finset.prod_le_prod (fun i _ => opNorm_nonneg' _) (fun i _ => ?_)
    unfold repF; rw [if_neg (by simp)]
    exact opNorm_QXQ hQH hQ _
  calc opNorm (repF Q A 0) * ∏ i : Fin m, opNorm (repF Q A i.succ)
      ≤ (opNorm (A (Fin.last (m+1))) * opNorm (A (Fin.castSucc 0))) * ∏ i : Fin m, opNorm (A (Fin.castSucc i.succ)) :=
        mul_le_mul h0 hs (Finset.prod_nonneg (fun i _ => opNorm_nonneg' _))
          (mul_nonneg (opNorm_nonneg' _) (opNorm_nonneg' _))
    _ = _ := by ring


lemma cycleFactor_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) : 0 ≤ cycleFactor β k := by
  unfold cycleFactor
  exact div_nonneg (Finset.prod_nonneg (fun l _ => by positivity)) (by positivity)

theorem norm_bound {d m Lc : ℕ} (ρ σ Q : Mat d) (hL : (labelledState ρ σ).PosSemidef)
    (hQH : Qᴴ = Q) (hQ : Q * Q = Q)
    (hS : (Q * plus ρ σ * Q).PosSemidef)
    (htr : ((Q * plus ρ σ * Q).trace).re ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ : opNorm (Q * plus ρ σ * Q) ≤ β)
    (hmin : Adm (Q * plus ρ σ * Q) (Q * minus ρ σ * Q))
    (c : Fin Lc → ℂ) (A : Fin Lc → Fin (m+2) → Mat d) (t : Fin Lc → Fin (m+1) → Bool) :
    weightedNormSq (labelledState ρ σ) (m+1) (symmetrize (hermPart (repKernel Q c A t))) ≤
      (∑ α, ‖c α‖ * ∏ i, opNorm (A α i)) ^ 2 * cycleFactor β (m+1) := by
  obtain ⟨B, hB⟩ := psd_factor (powerState_psd hL (m+1))
  have hwns : ∀ V, weightedNormSq (labelledState ρ σ) (m+1) V = ‖tw Bᴴ V‖ ^ 2 := by
    intro V; unfold weightedNormSq weightedInner; exact wns_eq_tw B hB V
  set cf := cycleFactor β (m+1) with hcf
  have hcf0 : 0 ≤ cf := cycleFactor_nonneg hβ0.le _
  set c0 : Equiv.Perm (Fin (m+1)) := (finRotate (m+1)).symm with hc0
  have hfull0 : ∀ x, ∃ n : ℕ, (c0 ^ n) 0 = x := by
    have := full_inv (finRotate (m+1)) 0 (full_rot m)
    simpa [hc0, Equiv.Perm.inv_def] using this
  have hfull1 : ∀ x, ∃ n : ℕ, (c0⁻¹ ^ n) 0 = x := full_inv c0 0 hfull0
  -- bound for each symmetrized cyclic kernel and its adjoint
  have hK : ∀ α, ‖tw Bᴴ (symmetrize (CK (repF Q (A α)) (t α)))‖ ≤ (∏ i, opNorm (A α i)) * Real.sqrt cf := by
    intro α
    rw [← Real.sqrt_sq (norm_nonneg _), ← hwns, CK_eq_GK]
    have h1 := sym_norm (by omega) ρ σ Q hQH hQ hS htr hβ0 hβ hmin c0 0 hfull0 (repF Q (A α))
      (repF_sandwich hQ (A α)) (t α)
    have h2 : (∏ i, opNorm (repF Q (A α) i)) ≤ ∏ i, opNorm (A α i) := repF_norm hQH hQ (A α)
    have h3 : 0 ≤ ∏ i, opNorm (repF Q (A α) i) := Finset.prod_nonneg (fun i _ => opNorm_nonneg' _)
    calc Real.sqrt (weightedNormSq (labelledState ρ σ) (m+1) (symmetrize (GK c0 (repF Q (A α)) (t α))))
        ≤ Real.sqrt ((∏ i, opNorm (repF Q (A α) i)) ^ 2 * cf) := Real.sqrt_le_sqrt h1
      _ = (∏ i, opNorm (repF Q (A α) i)) * Real.sqrt cf := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h3]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  have hKa : ∀ α, ‖tw Bᴴ (symmetrize (CK (repF Q (A α)) (t α))ᴴ)‖ ≤ (∏ i, opNorm (A α i)) * Real.sqrt cf := by
    intro α
    rw [← Real.sqrt_sq (norm_nonneg _), ← hwns, CK_eq_GK, GK_adj]
    set B' : Fin (m+1) → Mat d := fun l => (repF Q (A α) ((finRotate (m+1)).symm⁻¹ l))ᴴ with hB'
    have hB's : ∀ i, Q * B' i * Q = B' i := by
      intro i
      simp only [hB']
      conv_rhs => rw [← repF_sandwich hQ (A α)]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH]; simp only [Matrix.mul_assoc]
    have h1 := sym_norm (by omega) ρ σ Q hQH hQ hS htr hβ0 hβ hmin c0⁻¹ 0 hfull1 B' hB's (t α)
    have hprod : (∏ i, opNorm (B' i)) = ∏ i, opNorm (repF Q (A α) i) := by
      simp only [hB', opNorm_conj]
      exact Equiv.prod_comp _ (fun i => opNorm (repF Q (A α) i))
    have h2 : (∏ i, opNorm (repF Q (A α) i)) ≤ ∏ i, opNorm (A α i) := repF_norm hQH hQ (A α)
    have h3 : 0 ≤ ∏ i, opNorm (repF Q (A α) i) := Finset.prod_nonneg (fun i _ => opNorm_nonneg' _)
    rw [hprod] at h1
    calc Real.sqrt (weightedNormSq (labelledState ρ σ) (m+1) (symmetrize (GK c0⁻¹ B' (t α))))
        ≤ Real.sqrt ((∏ i, opNorm (repF Q (A α) i)) ^ 2 * cf) := Real.sqrt_le_sqrt h1
      _ = (∏ i, opNorm (repF Q (A α) i)) * Real.sqrt cf := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h3]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  -- decomposition
  have hdec : symmetrize (hermPart (repKernel Q c A t)) = ∑ α, ((c α / 2) • symmetrize (CK (repF Q (A α)) (t α)) +
      (star (c α) / 2) • symmetrize (CK (repF Q (A α)) (t α))ᴴ) := by
    unfold repKernel
    rw [hermPart_sum, symmetrize_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [symmetrize_add, symmetrize_smul, symmetrize_smul]
  have htw : ‖tw Bᴴ (symmetrize (hermPart (repKernel Q c A t)))‖ ≤
      (∑ α, ‖c α‖ * ∏ i, opNorm (A α i)) * Real.sqrt cf := by
    rw [hdec, tw_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun α _ => ?_)
    rw [tw_add, tw_smul, tw_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_div, norm_div, norm_star]
    have h2 : ‖(2:ℂ)‖ = 2 := by simp
    rw [h2]
    have := hK α; have := hKa α
    have hc0 : 0 ≤ ‖c α‖ := norm_nonneg _
    nlinarith
  rw [hwns]
  have h0 : 0 ≤ (∑ α, ‖c α‖ * ∏ i, opNorm (A α i)) * Real.sqrt cf :=
    mul_nonneg (Finset.sum_nonneg (fun α _ => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg (fun i _ => opNorm_nonneg' _)))) (Real.sqrt_nonneg _)
  calc ‖tw Bᴴ (symmetrize (hermPart (repKernel Q c A t)))‖ ^ 2
      ≤ ((∑ α, ‖c α‖ * ∏ i, opNorm (A α i)) * Real.sqrt cf) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htw 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hcf0]


lemma trace_powerState {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (n : ℕ) :
    (powerState τ n).trace = τ.trace ^ n := by
  simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.trace, Matrix.diag,
    Matrix.of_apply]
  have h := Fintype.prod_sum (fun (_ : Fin n) (i : ι) => τ i i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]

lemma trace_labelled {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, labelledState, if_true, Fintype.sum_prod_type,
    Fintype.sum_bool, if_false, Bool.false_eq_true]
  have h1 := hρ.2; have h2 := hσ.2
  simp only [Matrix.trace, Matrix.diag] at h1 h2
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, h2]; norm_num





lemma deg_subst {d : ℕ} (Q : Mat d) (g : TraceExpression d) :
    expressionDegree (substituteCompression Q g) = expressionDegree g := by
  rcases g with ⟨c0, ws⟩
  unfold expressionDegree substituteCompression
  simp only [List.map_map]
  congr 1
  refine List.map_congr_left (fun w _ => ?_)
  rcases w with ⟨fs, tl⟩
  cases fs with
  | nil => rfl
  | cons a l => simp

lemma expressionKernel_herm {d k : ℕ} (g : TraceExpression d) : (expressionKernel g k).IsHermitian := by
  unfold expressionKernel hermPart IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  simp

end OTDNorm

open MeasureTheory Matrix OptimalTraceDistance.Estimation OTDNorm in
theorem solution (d : ℕ) (hd : 0 < d)
    (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ)
    (Q : Mat d) (hQ : projector Q) (β : ℝ) (hβ : 0 < β)
    (hbound : opNorm (compress Q (plus ρ σ)) ≤ β)
    (g : TraceExpression d) (hg : realOnHermitian g) (M : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.Icc 1 (expressionDegree g),
      HasOrderedBound j (taylor g (compress Q (plus ρ σ)) (compress Q (minus ρ σ)) j) (M j))
    (n : ℕ) (hn : 0 < n) (hdegree : expressionDegree g ≤ n) :
  polynomialVariance (substituteCompression Q g) n ρ σ ≤
    ∑ j ∈ Finset.Icc 1 (expressionDegree g),
      (Nat.choose n j : ℝ)⁻¹ * (M j)^2 * cycleFactor β j := by
  set g' := substituteCompression Q g with hg'
  have hdeg : expressionDegree g' = expressionDegree g := deg_subst Q g
  set L := labelledState ρ σ
  have hL : L.PosSemidef := labelled_psd hρ hσ
  have hLtr : L.trace = 1 := trace_labelled hρ hσ
  -- facts about the compressed pair from Proposition 2.1
  obtain ⟨p1, -⟩ := proposition_2_1 d hd
  obtain ⟨-, -, -, -, -, hcomp⟩ := p1 ρ σ hρ hσ
  obtain ⟨hSpsd, hlo, hhi, hStr⟩ := hcomp Q hQ
  have hQH : Qᴴ = Q := hQ.1.eq
  have hQQ : Q * Q = Q := hQ.2
  have hmin : Adm (Q * plus ρ σ * Q) (Q * minus ρ σ * Q) := by
    refine ⟨?_, ?_, ?_⟩
    · have hMH : (minus ρ σ).IsHermitian := by
        unfold minus IsHermitian
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hρ.1.1.eq, hσ.1.1.eq]; simp
      unfold IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH, hMH.eq, Matrix.mul_assoc]
    · have := hlo; unfold lePSD compress at this
      rw [sub_neg_eq_add, add_comm] at this; exact this
    · have := hhi; unfold lePSD compress at this; exact this
  -- the Hoeffding bound
  unfold polynomialVariance observable
  have hsmul : (evaluate g' 0 0).re • (1 : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) =
      (((evaluate g' 0 0).re : ℝ) : ℂ) • 1 := by
    ext x y; simp [Matrix.smul_apply]
  rw [hsmul]
  have hH := variance_le_effective_generic L hL hLtr n (expressionDegree g') hn (by rw [hdeg]; exact hdegree)
    (fun k => expressionKernel g' k) (fun k _ => expressionKernel_herm g')
    (fun k _ π => expressionKernel_sym g' π) (evaluate g' 0 0).re
  refine hH.trans ?_
  nth_rw 1 [hdeg]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  -- the norm bound for B_j
  obtain ⟨Lc, c, A, t, hrep, hbd⟩ := hM j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hrep' : ∀ E₀ E₁ : Mat d, taylor g (Q * plus ρ σ * Q) (Q * minus ρ σ * Q) (m+1) E₀ E₁ =
      ∑ α, c α * ((List.ofFn (fun i : Fin (m+1) => A α i.castSucc * (if t α i then E₁ else E₀))).prod *
        A α (Fin.last (m+1))).trace := hrep
  have hid := identification ρ σ hρ.1.1 hσ.1.1 Q hQQ g c A t hrep'
  rw [show (fun k => expressionKernel g' k) = (fun k => expressionKernel (substituteCompression Q g) k) from rfl,
    hid]
  have hnb := norm_bound ρ σ Q hL hQH hQQ hSpsd hStr hβ (by unfold compress at hbound; exact hbound) hmin c A t
  refine hnb.trans ?_
  have hs0 : 0 ≤ ∑ α, ‖c α‖ * ∏ i, opNorm (A α i) :=
    Finset.sum_nonneg (fun α _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun i _ => opNorm_nonneg' _)))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hbd 2) (cycleFactor_nonneg hβ.le _)
