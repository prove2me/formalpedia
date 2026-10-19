-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.hadamard_influence_sampling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T23:24:39.749314+00:00
-- url     : https://prove2.me/submissions/c2771d03-5a31-46f8-a4cc-9295de8d3cd0

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model

/-!
A Hadamard on every wire realizes the product kernel. Real kernel orthogonality,
including a fixed output bit, gives the influence marginal for one labeled example.
The explicit register bijection then gives the independent repeated-example law.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

open QAlgorithms

namespace HadamardInfluence
open Classical

noncomputable def hgate {N : ℕ} (i : Fin N) : GateApp htcxGateSet N where
  gate := Gate.ofMatrix1 hadamard
  mem := by simp [htcxGateSet]
  wires := (show Fin 1 ↪ Fin N from ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩)

lemma act_hgate {N : ℕ} (i : Fin N) (ψ : EuclideanSpace ℂ (Qubits N)) (z : Qubits N) :
    act (embedOp (hgate i).gate.mat (hgate i).wires) ψ z =
      ∑ b : Bool, hadamard (z i) b * ψ (Function.update z i b) := by
  change (∑ x : Qubits N, _ * ψ x) = _
  rw [← Finset.sum_subset (s₁ := Finset.univ.image (fun b : Bool => Function.update z i b))
    (by simp)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b _
      have off (a : Fin N) (ha : a ∉ Set.range (hgate i).wires) :
          z a = Function.update z i b a := by
        have : a ≠ i := by intro h; subst a; exact ha ⟨(show Fin 1 from 0), rfl⟩
        simp [this]
      simp only [embedOp, Matrix.of_apply, if_pos off]
      change hadamard (z i) (Function.update z i b i) * ψ _ = _
      rw [Function.update_self]
    · intro a _ b _ h
      simpa using congrFun h i
  · intro x _ hx
    have off : ¬ (∀ a : Fin N, a ∉ Set.range (hgate i).wires → z a = x a) := by
      intro h; apply hx
      apply Finset.mem_image.mpr
      refine ⟨x i, Finset.mem_univ _, ?_⟩
      funext a
      by_cases ha : a = i
      · subst a; simp
      · have hr : a ∉ Set.range (hgate i).wires := by
          rintro ⟨b, hb⟩
          exact ha (show a = i from hb.symm)
        simp [ha, h a hr]
    simp only [embedOp, Matrix.of_apply, if_neg off, zero_mul]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : act (A * B) ψ = act A (act B ψ) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm

lemma act_append {N : ℕ} (c d : Circuit htcxGateSet N) (ψ : EuclideanSpace ℂ (Qubits N)) :
    act (c ++ d).unitary ψ = act d.unitary (act c.unitary ψ) := by
  rw [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append, act_mul]
  rfl

lemma hgate_product {N : ℕ} (i : Fin N) (v : Fin N → Bool → ℂ) (z : Qubits N) :
    (∑ b : Bool, hadamard (z i) b * ∏ p : Fin N, v p (Function.update z i b p)) =
      ∏ p : Fin N, if p = i then (∑ b : Bool, hadamard (z p) b * v p b) else v p (z p) := by
  have hp (b : Bool) : (∏ p : Fin N, v p (Function.update z i b p)) =
      v i b * ∏ p ∈ Finset.univ.erase i, v p (z p) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    simp [Finset.ne_of_mem_erase hp]
  simp_rw [hp, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  simp [Finset.ne_of_mem_erase hp]

lemma tensor_circuit (N : ℕ) :
    ∃ c : Circuit htcxGateSet N, c.size = N ∧
      ∀ v : Fin N → Bool → ℂ, ∀ z : Qubits N,
        act c.unitary (WithLp.toLp 2 fun x => ∏ p, v p (x p)) z =
          ∏ p, ∑ b : Bool, hadamard (z p) b * v p b := by
  have hs (s : Finset (Fin N)) : ∃ c : Circuit htcxGateSet N, c.size = s.card ∧
      ∀ v : Fin N → Bool → ℂ, ∀ z : Qubits N,
        act c.unitary (WithLp.toLp 2 fun x => ∏ p, v p (x p)) z =
          ∏ p, if p ∈ s then (∑ b : Bool, hadamard (z p) b * v p b) else v p (z p) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨[], rfl, ?_⟩
      intro v z
      simp [Circuit.unitary, act]
    | @insert i s hi ih =>
      obtain ⟨c, hc, hv⟩ := ih
      refine ⟨c ++ [hgate i], ?_, ?_⟩
      · simpa [Circuit.size, Finset.card_insert_of_notMem hi] using hc
      · intro v z
        rw [act_append]
        have he : act c.unitary (WithLp.toLp 2 fun x => ∏ p, v p (x p)) =
            WithLp.toLp 2 (fun x => ∏ p, (if p ∈ s then (fun a => ∑ b : Bool, hadamard a b * v p b) else v p) (x p)) := by
          ext x
          simpa only [PiLp.toLp_apply, ite_apply] using hv v x
        rw [he]
        simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
        rw [act_hgate]
        simp only
        rw [hgate_product]
        apply Finset.prod_congr rfl
        intro p _
        by_cases hp : p = i
        · subst p; simp [hi]
        · by_cases hps : p ∈ s <;> simp [hp, hps]
  obtain ⟨c, hc, hv⟩ := hs Finset.univ
  exact ⟨c, by simpa using hc, by simpa using hv⟩

lemma tensor_circuit_matrix (N : ℕ) :
    ∃ c : Circuit htcxGateSet N, c.size = N ∧
      ∀ z x : Qubits N, c.unitary z x = ∏ p, hadamard (z p) (x p) := by
  obtain ⟨c, hc, hv⟩ := tensor_circuit N
  refine ⟨c, hc, ?_⟩
  intro z x
  have hk : (WithLp.toLp 2 fun y : Qubits N => ∏ p, if y p = x p then (1 : ℂ) else 0) = ket x := by
    ext y
    by_cases hy : y = x
    · subst y; simp [ket]
    · have ⟨p, hp⟩ := Function.ne_iff.mp hy
      simp only [ket, PiLp.single_apply, if_neg hy]
      exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
  have h := hv (fun p b => if b = x p then 1 else 0) z
  rw [hk] at h
  simpa [act, ket, EuclideanSpace.inner_single_left] using h

end HadamardInfluence
open QAlgorithms
namespace HadamardMath
open Classical

noncomputable def hr (a b : Bool) : ℝ := if a && b then -(Real.sqrt 2)⁻¹ else (Real.sqrt 2)⁻¹

lemma hr_complex (a b : Bool) : (hr a b : ℂ) = hadamard a b := by
  cases a <;> cases b <;> simp [hr, hadamard]

lemma hr_orth (a b : Bool) : (∑ c : Bool, hr c a * hr c b) = if a = b then 1 else 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  cases a <;> cases b <;> simp [hr] <;> field_simp <;> nlinarith

lemma hr_zero (a b : Bool) :
    (∑ c : Bool, if c = false then hr c a * hr c b else 0) = 1 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  cases a <;> cases b <;> simp [hr] <;> field_simp <;> nlinarith

noncomputable def K {m : ℕ} (y x : Qubits m) : ℝ := ∏ p, hr (y p) (x p)

lemma orth {m : ℕ} (x u : Qubits m) :
    (∑ y : Qubits m, K y x * K y u) = if x = u then 1 else 0 := by
  simp only [K, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun p b => hr b (x p) * hr b (u p))]
  simp_rw [hr_orth]
  by_cases h : x = u
  · subst u; simp
  · rw [if_neg h]
    obtain ⟨p, hp⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

lemma masked_orth {m : ℕ} (i : Fin m) (x u : Qubits m) :
    (∑ y : Qubits m, if y i = false then K y x * K y u else 0) =
      if (∀ p, p ≠ i → x p = u p) then 1 / 2 else 0 := by
  have he (y : Qubits m) : (if y i = false then K y x * K y u else 0) =
      ∏ p : Fin m, if p = i then (if y p = false then hr (y p) (x p) * hr (y p) (u p) else 0)
        else hr (y p) (x p) * hr (y p) (u p) := by
    by_cases hy : y i = false
    · simp only [hy, if_true, K, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p = i <;> simp [hp, hy]
    · rw [if_neg hy]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hy])
  simp_rw [he]
  rw [← Fintype.prod_sum (fun p b => if p = i then (if b = false then hr b (x p) * hr b (u p) else 0) else hr b (x p) * hr b (u p))]
  have hh (p : Fin m) :
      (∑ b : Bool, if p = i then (if b = false then hr b (x p) * hr b (u p) else 0)
        else hr b (x p) * hr b (u p)) =
      if p = i then 1 / 2 else if x p = u p then 1 else 0 := by
    by_cases hp : p = i
    · simp only [if_pos hp]; exact hr_zero _ _
    · simp only [if_neg hp]; exact hr_orth _ _
  simp_rw [hh]
  by_cases h : ∀ p, p ≠ i → x p = u p
  · rw [if_pos h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true]
    rw [show (∏ p ∈ Finset.univ.erase i, if p = i then (1:ℝ) / 2 else if x p = u p then 1 else 0) = 1 by
      apply Finset.prod_eq_one
      intro p hp
      simp [Finset.ne_of_mem_erase hp, h p (Finset.ne_of_mem_erase hp)]]
    simp
  · rw [if_neg h]
    push Not at h
    obtain ⟨p, hpi, hp⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hpi, hp])

noncomputable def transform {m : ℕ} (a : Qubits m → ℝ) (y : Qubits m) : ℝ :=
  ∑ x, K y x * a x

lemma expansion {m : ℕ} (a : Qubits m → ℝ) (w : Qubits m → ℝ) :
    (∑ y, w y * (transform a y)^2) =
      ∑ x, ∑ u, a x * a u * ∑ y, w y * (K y x * K y u) := by
  simp only [transform, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma parseval {m : ℕ} (a : Qubits m → ℝ) :
    (∑ y, (transform a y)^2) = ∑ x, (a x)^2 := by
  have h := expansion a (fun _ => 1)
  simp only [one_mul, orth] at h
  simpa [mul_ite, pow_two] using h

lemma two_fiber {m : ℕ} (i : Fin m) (x : Qubits m) (g : Qubits m → ℝ) :
    (∑ u, if (∀ p, p ≠ i → x p = u p) then g u else 0) =
      g (Function.update x i false) + g (Function.update x i true) := by
  rw [← Finset.sum_subset (s₁ := Finset.univ.image (fun b : Bool => Function.update x i b)) (by simp)]
  · rw [Finset.sum_image]
    · simp only [Fintype.sum_bool]
      have he (b : Bool) : ∀ p, p ≠ i → x p = Function.update x i b p := by
        intro p hp; simp [hp]
      simp only [if_pos (he _)]
      ring
    · intro a _ b _ h; simpa using congrFun h i
  · intro u _ hu
    rw [if_neg]
    intro h
    apply hu
    refine Finset.mem_image.mpr ⟨u i, Finset.mem_univ _, ?_⟩
    funext p
    by_cases hp : p = i
    · subst p; simp
    · simp [hp, h p hp]

lemma zero_mass {m : ℕ} (a : Qubits m → ℝ) (i : Fin m) :
    (∑ y, if y i = false then (transform a y)^2 else 0) =
      ((∑ x, (a x)^2) + ∑ x, a x * a (Function.update x i (!x i))) / 2 := by
  have he := expansion a (fun y => if y i = false then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul, masked_orth] at he
  rw [he]
  simp_rw [mul_ite, mul_zero]
  simp_rw [two_fiber]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  have hx : Function.update x i (x i) = x := Function.update_eq_self i x
  cases hi : x i
  · have hfalse : Function.update x i false = x := by simp [hi]
    simp [hfalse]; ring
  · have htrue : Function.update x i true = x := by simp [hi]
    simp [htrue]; ring

noncomputable def alpha (n : ℕ) (f : Qubits n → Bool) (z : Qubits (n+1)) : ℝ :=
  if z (Fin.last n) = f (Fin.init z) then ((Real.sqrt 2)^n)⁻¹ else 0

lemma snoc_sum {n : ℕ} (g : Qubits (n+1) → ℝ) :
    (∑ z, g z) = ∑ x : Qubits n, ∑ b : Bool, g (Fin.snoc (α := fun _ => Bool) x b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma alpha_norm (n : ℕ) (f : Qubits n → Bool) :
    (∑ z, (alpha n f z)^2) = 1 := by
  rw [snoc_sum]
  have he (x : Qubits n) : (∑ b : Bool, (alpha n f (Fin.snoc (α := fun _ => Bool) x b))^2) = (((Real.sqrt 2)^n)⁻¹)^2 := by
    simp only [alpha, Fin.snoc_last, Fin.init_snoc]
    cases f x <;> norm_num
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  have hn : Real.sqrt (2:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  push_cast
  rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, hs]
  field_simp

lemma snoc_flip {n : ℕ} (x : Qubits n) (b : Bool) (i : Fin n) :
    Function.update (Fin.snoc (α := fun _ => Bool) x b) i.castSucc (!(Fin.snoc (α := fun _ => Bool) x b) i.castSucc) =
      Fin.snoc (α := fun _ => Bool) (Function.update x i (!x i)) b := by
  funext p
  refine Fin.lastCases ?_ (fun j => ?_) p
  · have hne : Fin.last n ≠ i.castSucc := by
      intro h; have hval := congrArg Fin.val h; simp at hval; omega
    simp only [Function.update_of_ne hne, Fin.snoc_last]
  · by_cases hj : j = i
    · subst j; simp
    · simp [Fin.castSucc_inj, hj]

lemma alpha_correlation (n : ℕ) (f : Qubits n → Bool) (i : Fin n) :
    (∑ z, alpha n f z * alpha n f (Function.update z i.castSucc (!z i.castSucc))) =
      1 - ((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0 := by
  rw [snoc_sum]
  simp_rw [snoc_flip]
  have he (x : Qubits n) :
      (∑ b : Bool, alpha n f (Fin.snoc (α := fun _ => Bool) x b) * alpha n f (Fin.snoc (α := fun _ => Bool) (Function.update x i (!x i)) b)) =
        if f (Function.update x i (!x i)) = f x then (((Real.sqrt 2)^n)⁻¹)^2 else 0 := by
    simp only [alpha, Fin.snoc_last, Fin.init_snoc]
    cases f x <;> cases f (Function.update x i (!x i)) <;> norm_num [pow_two]
  simp_rw [he]
  have hconst : (((Real.sqrt 2)^n)⁻¹)^2 = ((2:ℝ)^n)⁻¹ := by
    have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
    rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, hs]
  rw [hconst]
  have htotal : (∑ x : Qubits n, (if f (Function.update x i (!x i)) = f x then ((2:ℝ)^n)⁻¹ else 0) +
      ((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) = 1 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero]
    have heq (x : Qubits n) :
        (if f (Function.update x i (!x i)) = f x then ((2:ℝ)^n)⁻¹ else 0) +
        (if f (Function.update x i (!x i)) ≠ f x then ((2:ℝ)^n)⁻¹ else 0) = ((2:ℝ)^n)⁻¹ := by
      by_cases h : f (Function.update x i (!x i)) = f x <;> simp [h]
    simp_rw [heq]
    simp [Fintype.card_bool, Fintype.card_fin]
  linarith

lemma single_normalized (n : ℕ) (f : Qubits n → Bool) :
    (∑ z, (transform (alpha n f) z)^2) = 1 := by rw [parseval, alpha_norm]

lemma single_zero (n : ℕ) (f : Qubits n → Bool) (i : Fin n) :
    (∑ z, if z i.castSucc = false then (transform (alpha n f) z)^2 else 0) =
      1 - (((2:ℝ)^n)⁻¹ * ∑ x : Qubits n, if f (Function.update x i (!x i)) ≠ f x then (1:ℝ) else 0) / 2 := by
  rw [zero_mass, alpha_norm, alpha_correlation]
  ring

end HadamardMath
open QAlgorithms QAlgorithms.LearningSurvey
namespace HadamardBlocks
open Classical HadamardMath

def wires (n T : ℕ) : Fin (T*(n+1)+0) ≃ Fin T × Fin (n+1) :=
  (finCongr (Nat.add_zero _)).trans finProdFinEquiv.symm

def blocks (n T : ℕ) : Qubits (T*(n+1)+0) ≃ (Fin T → Qubits (n+1)) :=
  (Equiv.arrowCongr (wires n T) (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

lemma blocks_apply {n T : ℕ} (z : Qubits (T*(n+1)+0)) (j : Fin T) (p : Fin (n+1)) :
    blocks n T z j p = z ((wires n T).symm (j,p)) := rfl

lemma wire_value {n T : ℕ} (j : Fin T) (p : Fin (n+1)) :
    ((wires n T).symm (j,p) : ℕ) = (j:ℕ)*(n+1)+(p:ℕ) := by
  simp [wires, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

lemma input_block {n T : ℕ} (z : Qubits (T*(n+1)+0)) (j : Fin T) :
    exInput n z j = Fin.init (blocks n T z j) := by
  funext i
  unfold exInput regBit Fin.init
  have hv := wire_value j i.castSucc
  have hp := ((wires n T).symm (j,i.castSucc)).isLt
  simp only [Fin.val_castSucc] at hv
  have hlt : (j:ℕ)*(n+1)+(i:ℕ) < T*(n+1)+0 := by omega
  rw [dif_pos hlt, blocks_apply]
  congr 1
  apply Fin.ext
  exact hv.symm

lemma label_block {n T : ℕ} (z : Qubits (T*(n+1)+0)) (j : Fin T) :
    exLabel n z j = blocks n T z j (Fin.last n) := by
  unfold exLabel regBit
  have hv := wire_value j (Fin.last n)
  have hp := ((wires n T).symm (j,Fin.last n)).isLt
  simp only [Fin.val_last] at hv
  have hlt : (j:ℕ)*(n+1)+n < T*(n+1)+0 := by omega
  rw [dif_pos hlt, blocks_apply]
  congr 1
  apply Fin.ext
  exact hv.symm

lemma kernel_blocks {n T : ℕ} (z x : Qubits (T*(n+1)+0)) :
    K z x = ∏ j : Fin T, K (blocks n T z j) (blocks n T x j) := by
  unfold K
  rw [← (wires n T).symm.prod_comp]
  rw [Fintype.prod_prod_type]
  rfl

lemma tensor_transform {n T : ℕ} (a : Qubits (n+1) → ℝ) (z : Qubits (T*(n+1)+0)) :
    transform (fun x => ∏ j : Fin T, a (blocks n T x j)) z =
      ∏ j : Fin T, transform a (blocks n T z j) := by
  unfold transform
  simp_rw [kernel_blocks, ← Finset.prod_mul_distrib]
  rw [← (blocks n T).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  exact (Fintype.prod_sum (fun j x => K (blocks n T z j) x * a x)).symm

lemma examples_product (n T : ℕ) (f : Qubits n → Bool) (z : Qubits (T*(n+1)+0)) :
    juntaExamplesState n T 0 f z = ((∏ j : Fin T, alpha n f (blocks n T z j) : ℝ) : ℂ) := by
  have hanc : ∀ p : Fin (T*(n+1)+0), T*(n+1) ≤ (p:ℕ) → z p = false := by
    intro p hp; have := p.isLt; omega
  simp only [juntaExamplesState, PiLp.toLp_apply,
    input_block, label_block, alpha, Finset.prod_ite_zero, Finset.mem_univ, forall_const]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases h : ∀ j : Fin T, blocks n T z j (Fin.last n) = f (Fin.init (blocks n T z j))
  · rw [if_pos ⟨hanc, h⟩, if_pos h]
  · rw [if_neg (fun ha => h ha.2), if_neg h]; simp

lemma outcome_product {n T : ℕ} (c : Circuit htcxGateSet (T*(n+1)+0))
    (hc : ∀ z x, c.unitary z x = ∏ p, hadamard (z p) (x p))
    (f : Qubits n → Bool) (z : Qubits (T*(n+1)+0)) :
    prob (act c.unitary (juntaExamplesState n T 0 f)) z =
      ∏ j : Fin T, (transform (alpha n f) (blocks n T z j))^2 := by
  have ha : act c.unitary (juntaExamplesState n T 0 f) z =
      ((transform (fun x => ∏ j : Fin T, alpha n f (blocks n T x j)) z : ℝ) : ℂ) := by
    change (∑ x, c.unitary z x * juntaExamplesState n T 0 f x) = _
    simp_rw [hc, examples_product]
    simp only [transform, K, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, hr_complex]
  simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul, ha,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [tensor_transform, Finset.prod_pow]

lemma total_product {n T : ℕ} (p : Qubits (n+1) → ℝ) :
    (∑ z : Qubits (T*(n+1)+0), ∏ j : Fin T, p (blocks n T z j)) = (∑ y, p y)^T := by
  rw [← (blocks n T).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [← Fintype.prod_sum (fun _ : Fin T => p)]
  simp

lemma absence_product {n T : ℕ} (p : Qubits (n+1) → ℝ) (i : Fin n) :
    (∑ z : Qubits (T*(n+1)+0), if (∀ j : Fin T, exInput n z j i = false)
      then ∏ j : Fin T, p (blocks n T z j) else 0) =
      (∑ y : Qubits (n+1), if y i.castSucc = false then p y else 0)^T := by
  have he (z : Qubits (T*(n+1)+0)) :
      (if ∀ j : Fin T, exInput n z j i = false then ∏ j : Fin T, p (blocks n T z j) else 0) =
      ∏ j : Fin T, if blocks n T z j i.castSucc = false then p (blocks n T z j) else 0 := by
    rw [Finset.prod_ite_zero]
    simp [input_block, Fin.init]
  simp_rw [he]
  exact total_product (n := n) (T := T) (fun y => if y i.castSucc = false then p y else 0)

end HadamardBlocks

open HadamardInfluence HadamardMath HadamardBlocks

theorem solution (n T : ℕ) :
    ∃ c : QAlgorithms.Circuit QAlgorithms.htcxGateSet (T * (n + 1) + 0),
      c.size ≤ T * (n + 1) ∧
      ∀ f : QAlgorithms.Qubits n → Bool,
        let P := fun z => QAlgorithms.prob
          (QAlgorithms.act c.unitary (QAlgorithms.LearningSurvey.juntaExamplesState n T 0 f)) z
        (∑ z, P z) = 1 ∧
        ∀ i : Fin n,
          (∑ z, if (∀ j : Fin T, QAlgorithms.LearningSurvey.exInput n z j i = false)
            then P z else 0) =
          (1 - (((2 : ℝ)^n)⁻¹ * ∑ x : QAlgorithms.Qubits n,
            if f (Function.update x i (!x i)) ≠ f x then (1 : ℝ) else 0) / 2)^T := by
  obtain ⟨c, hsize, hc⟩ := tensor_circuit_matrix (T*(n+1)+0)
  refine ⟨c, by omega, ?_⟩
  intro f
  dsimp only
  simp_rw [outcome_product c hc f]
  constructor
  · rw [total_product (n := n) (T := T) (fun y => (transform (alpha n f) y)^2), single_normalized, one_pow]
  · intro i
    rw [absence_product (n := n) (T := T) (fun y => (transform (alpha n f) y)^2) i, single_zero]
