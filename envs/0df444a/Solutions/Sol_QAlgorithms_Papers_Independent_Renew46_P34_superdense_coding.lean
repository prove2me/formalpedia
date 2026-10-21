-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.superdense_coding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:54:32.574589+00:00
-- url     : https://prove2.me/submissions/83d624a5-e3a6-4a64-b33a-82133e1cfbb0

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P34

instance g64g_uq : Unique (Qubits 0) := Pi.uniqueOfIsEmpty _

lemma g64g_kr {K ι κ : Type} [Fintype K] [Fintype ι] (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) (i j : κ) :
    krausApply E ρ i j = ∑ k, ∑ a, ∑ b, E k i a * ρ a b * conj (E k j b) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]; rfl

lemma g64g_s1 (f : Qubits 1 → ℂ) : ∑ b, f b = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]; rfl

lemma g64g_s2 (f : Qubits 2 → ℂ) : ∑ b, f b = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  simp [finTwoArrowEquiv]; ring

def g64g_pz (x : Qubits 2) (q a : Bool) : ℂ := if q = xor a (x 0) then (if (x 1 && a) then -1 else 1) else 0

def g64g_g (k : Fin 4) : Qubits 2 := ![decide (k.val % 2 = 1), decide (k.val / 2 = 1)]

def g64g_E : Fin 4 → Matrix (Unit × (Fin 1 × (Qubits 1 × Qubits 0))) ((Qubits 0 × Qubits 2) × (Unit × Qubits 1)) ℂ :=
  fun k o i => if i.1.2 = g64g_g k then g64g_pz (g64g_g k) (o.2.2.1 0) (i.2.2 0) else 0

def g64g_c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def g64g_B : Fin 1 → Matrix (Qubits 0 × (Qubits 2 × Qubits 0)) (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) ℂ :=
  fun _ o i => g64g_pz o.2.1 (i.2.2.2.1 0) (i.2.2.1 0) * g64g_c

def g64g_A : Fin 1 → Matrix (Qubits 0) (Unit × Fin 1) ℂ := fun _ _ _ => 1

def g64g_enc : Superop ((Qubits 0 × Qubits 2) × (Unit × Qubits 1)) (Unit × (Fin 1 × (Qubits 1 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ∑ k : Fin 4, ∑ a : Qubits 1, ∑ a' : Qubits 1,
    g64g_pz (g64g_g k) (o.2.2.1 0) (a 0) * ρ ((default, g64g_g k), ((), a)) ((default, g64g_g k), ((), a')) *
      g64g_pz (g64g_g k) (o'.2.2.1 0) (a' 0)

def g64g_ali : Superop (Unit × Fin 1) (Qubits 0) := fun ρ => Matrix.of fun _ _ => ρ ((), 0) ((), 0)

def g64g_bob : Superop (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) (Qubits 0 × (Qubits 2 × Qubits 0)) :=
  fun ρ => Matrix.of fun o o' => ∑ e : Qubits 1, ∑ q : Qubits 1, ∑ e' : Qubits 1, ∑ q' : Qubits 1,
    g64g_pz o.2.1 (q 0) (e 0) * g64g_c * ρ ((), ((), (e, (q, default)))) ((), ((), (e', (q', default)))) *
      (g64g_pz o'.2.1 (q' 0) (e' 0) * g64g_c)

lemma g64g_feq (a b : Bool) : ((fun _ : Fin 1 => a) = (fun _ => b)) = (a = b) := by
  apply propext; constructor
  · intro h; exact congrFun h 0
  · intro h; rw [h]

lemma g64g_c2 : g64g_c * g64g_c = 1 / 2 := by
  unfold g64g_c
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma g64g_veq (a b c d : Bool) : (![a, b] = ![c, d]) = (a = c ∧ b = d) := by
  apply propext; constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma g64g_pzc (x : Qubits 2) (q a : Bool) : (starRingEnd ℂ) (g64g_pz x q a) = g64g_pz x q a := by
  unfold g64g_pz; split_ifs <;> simp

lemma g64g_cc : (starRingEnd ℂ) g64g_c = g64g_c := by
  unfold g64g_c; rw [map_inv₀, Complex.conj_ofReal]

lemma g64g_x2 (x : Qubits 2) : x = ![x 0, x 1] := by funext t; fin_cases t <;> rfl
lemma g64g_x1 (x : Qubits 1) : x = fun _ => x 0 := by funext t; fin_cases t; rfl

lemma g64g_E_kraus : IsKrausFamily g64g_E := by
  unfold IsKrausFamily
  ext ⟨⟨u, x⟩, ⟨w, e⟩⟩ ⟨⟨u', x'⟩, ⟨w', e'⟩⟩
  rw [g64g_x2 x, g64g_x2 x', g64g_x1 e, g64g_x1 e']
  generalize x 0 = a0, x 1 = a1, x' 0 = b0, x' 1 = b1, e 0 = c0, e' 0 = d0
  obtain rfl : u = u' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g64g_s1, Fin.sum_univ_four, Matrix.one_apply]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases d0 <;>
    simp [g64g_E, g64g_pz, g64g_g, g64g_veq, g64g_feq] <;> norm_num

lemma g64g_enc_eq (ρ : Matrix ((Qubits 0 × Qubits 2) × (Unit × Qubits 1)) ((Qubits 0 × Qubits 2) × (Unit × Qubits 1)) ℂ) :
    g64g_enc ρ = krausApply g64g_E ρ := by
  ext o o'
  rw [g64g_kr]
  simp only [g64g_enc, g64g_E, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Finset.sum_ite_eq', g64g_pzc, apply_ite (starRingEnd ℂ)]
  have key : ∀ a : Qubits 1, (((fun _ => false : Qubits 0), g64g_g k), ((), a)) =
      (((default : Qubits 0), g64g_g k), (PUnit.unit, a)) :=
    fun a => Prod.ext (Prod.ext (Subsingleton.elim _ _) rfl) rfl
  simp only [key]
  congr!

lemma g64g_A_kraus : IsKrausFamily g64g_A := by
  unfold IsKrausFamily
  ext a b
  rw [Subsingleton.elim a b]
  simp [g64g_A, Matrix.mul_apply]

lemma g64g_ali_eq (ρ : Matrix (Unit × Fin 1) (Unit × Fin 1) ℂ) : g64g_ali ρ = krausApply g64g_A ρ := by
  ext o o'
  rw [g64g_kr]
  simp [g64g_ali, g64g_A, Fintype.sum_prod_type]

lemma g64g_B_kraus : IsKrausFamily g64g_B := by
  unfold IsKrausFamily
  ext ⟨u, w, e, q, c⟩ ⟨u', w', e', q', c'⟩
  rw [g64g_x1 e, g64g_x1 e', g64g_x1 q, g64g_x1 q']
  generalize e 0 = a0, e' 0 = b0, q 0 = c0, q' 0 = d0
  obtain rfl : c = c' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g64g_s2, Fin.sum_univ_one, Matrix.one_apply]
  have hc2 := g64g_c2
  cases a0 <;> cases b0 <;> cases c0 <;> cases d0 <;>
    simp [g64g_B, g64g_pz, g64g_feq, g64g_cc] <;> (ring_nf; try rw [show g64g_c ^ 2 = 1 / 2 by rw [sq, g64g_c2]]; try norm_num)

lemma g64g_bob_eq (ρ : Matrix (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) ℂ) :
    g64g_bob ρ = krausApply g64g_B ρ := by
  ext o o'
  rw [g64g_kr]
  simp only [g64g_bob, g64g_B, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    map_mul, g64g_pzc, g64g_cc]
  congr!

abbrev g64g_P : OneWayCode Unit Unit Unit Unit Unit (TaskInput 0 2) (Qubits 0) (TaskBob 0 2 0) where
  e := 1
  q := 1
  c := 0
  memory := 1
  memoryPositive := by norm_num
  encoder := g64g_enc
  aliceDecoder := g64g_ali
  bobDecoder := g64g_bob
  encoderChannel := ⟨4, g64g_E, by convert g64g_E_kraus, fun ρ => by convert g64g_enc_eq ρ⟩
  aliceChannel := ⟨1, g64g_A, by convert g64g_A_kraus, fun ρ => by convert g64g_ali_eq ρ⟩
  bobChannel := ⟨1, g64g_B, by convert g64g_B_kraus, fun ρ => by convert g64g_bob_eq ρ⟩

theorem solution : ExactConversion emptyResource 1 1 0 (taskTarget 0 2 0) := by
  refine ⟨g64g_P, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g64g_P, g64g_enc, g64g_ali, g64g_bob,
    Matrix.of_apply, initialCodeState, emptyResource, forwardResource, taskTarget]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  simp only [Matrix.of, Equiv.refl, Equiv.coe_fn_mk, id_eq, e1, if_true]
  obtain ⟨u0, u1, x, u2⟩ := i
  obtain ⟨v0, v1, y, v2⟩ := j
  obtain rfl : u1 = default := Subsingleton.elim _ _
  obtain rfl : v1 = default := Subsingleton.elim _ _
  have hx : x = ![x 0, x 1] := by funext t; fin_cases t <;> rfl
  have hy : y = ![y 0, y 1] := by funext t; fin_cases t <;> rfl
  rw [hx, hy]
  generalize x 0 = a0, x 1 = a1, y 0 = b0, y 1 = b1
  simp only [g64g_s1, Fin.sum_univ_four, pow_one, pow_zero, Real.sqrt_one, Complex.ofReal_one, inv_one]
  have hc : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = g64g_c := rfl
  simp only [hc]
  have hcc : (starRingEnd ℂ) g64g_c = g64g_c := by
    unfold g64g_c; rw [map_inv₀, Complex.conj_ofReal]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    simp [g64g_pz, g64g_g, g64g_feq, e1, hcc]
  all_goals
    have hc4 : g64g_c ^ 4 = 1 / 4 := by
      rw [show g64g_c ^ 4 = (g64g_c * g64g_c) * (g64g_c * g64g_c) by ring, g64g_c2]; norm_num
    ring_nf
    rw [hc4]
    ring
