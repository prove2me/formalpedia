-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.teleportation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:11:59.734881+00:00
-- url     : https://prove2.me/submissions/21f0174b-5789-4953-b0e0-06b54de793c8

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


def g64g_c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹


def g64g_A : Fin 1 → Matrix (Qubits 0) (Unit × Fin 1) ℂ := fun _ _ _ => 1


def g64g_ali : Superop (Unit × Fin 1) (Qubits 0) := fun ρ => Matrix.of fun _ _ => ρ ((), 0) ((), 0)


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

lemma g64g_A_kraus : IsKrausFamily g64g_A := by
  unfold IsKrausFamily
  ext a b
  rw [Subsingleton.elim a b]
  simp [g64g_A, Matrix.mul_apply]

lemma g64g_ali_eq (ρ : Matrix (Unit × Fin 1) (Unit × Fin 1) ℂ) : g64g_ali ρ = krausApply g64g_A ρ := by
  ext o o'
  rw [g64g_kr]
  simp [g64g_ali, g64g_A, Fintype.sum_prod_type]


def g64p_E : Fin 4 → Matrix (Unit × (Fin 1 × (Qubits 0 × Qubits 2))) ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ℂ :=
  fun k o i => if o.2.2.2 = g64g_g k then g64g_c * g64g_pz (g64g_g k) (i.2.2 0) (i.1.1 0) else 0

def g64p_B : Fin 4 → Matrix (Qubits 1 × (Qubits 0 × Qubits 0)) (Unit × (Unit × (Qubits 1 × (Qubits 0 × Qubits 2)))) ℂ :=
  fun k o i => if i.2.2.2.2 = g64g_g k then g64g_pz (g64g_g k) (i.2.2.1 0) (o.1 0) else 0

lemma g64p_E_kraus : IsKrausFamily g64p_E := by
  unfold IsKrausFamily
  ext ⟨⟨x, z⟩, ⟨u, e⟩⟩ ⟨⟨x', z'⟩, ⟨u', e'⟩⟩
  rw [g64g_x1 x, g64g_x1 x', g64g_x1 e, g64g_x1 e']
  generalize x 0 = a0, x' 0 = b0, e 0 = c0, e' 0 = d0
  obtain rfl : u = u' := Subsingleton.elim _ _
  obtain rfl : z = z' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g64g_s2, Fin.sum_univ_four, Matrix.one_apply]
  have hc2 := g64g_c2
  cases a0 <;> cases b0 <;> cases c0 <;> cases d0 <;>
    simp [g64p_E, g64g_pz, g64g_g, g64g_veq, g64g_feq, g64g_cc] <;>
    (ring_nf; try rw [show g64g_c ^ 2 = 1 / 2 by rw [sq, g64g_c2]]; try norm_num)

lemma g64p_B_kraus : IsKrausFamily g64p_B := by
  unfold IsKrausFamily
  ext ⟨u, w, e, z, m⟩ ⟨u', w', e', z', m'⟩
  rw [g64g_x1 e, g64g_x1 e', g64g_x2 m, g64g_x2 m']
  generalize e 0 = a0, e' 0 = b0, m 0 = c0, m 1 = c1, m' 0 = d0, m' 1 = d1
  obtain rfl : u = u' := Subsingleton.elim _ _
  obtain rfl : w = w' := Subsingleton.elim _ _
  obtain rfl : z = z' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g64g_s1, Fin.sum_univ_four, Matrix.one_apply]
  cases a0 <;> cases b0 <;> cases c0 <;> cases c1 <;> cases d0 <;> cases d1 <;>
    simp [g64p_B, g64g_pz, g64g_g, g64g_veq, g64g_feq]

abbrev g64p_P : OneWayCode Unit Unit Unit Unit Unit (TaskInput 1 0) (Qubits 0) (TaskBob 1 0 0) where
  e := 1
  q := 0
  c := 2
  memory := 1
  memoryPositive := by norm_num
  encoder := krausApply g64p_E
  aliceDecoder := g64g_ali
  bobDecoder := krausApply g64p_B
  encoderChannel := ⟨4, g64p_E, by convert g64p_E_kraus, fun ρ => rfl⟩
  aliceChannel := ⟨1, g64g_A, by convert g64g_A_kraus, fun ρ => by convert g64g_ali_eq ρ⟩
  bobChannel := ⟨4, g64p_B, by convert g64p_B_kraus, fun ρ => rfl⟩

theorem g64p_main :
    ExactConversion emptyResource 1 0 2 (taskTarget 1 0 0) := by
  refine ⟨g64p_P, rfl, rfl, rfl, ?_⟩
  have hk : ∀ (ρ : ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) → ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) → ℂ)
      (o o' : Unit × (Fin 1 × (Qubits 0 × Qubits 2))),
      krausApply g64p_E ρ o o' = ∑ k, ∑ a, ∑ b, g64p_E k o a * ρ a b * (starRingEnd ℂ) (g64p_E k o' b) :=
    fun ρ o o' => g64g_kr g64p_E ρ o o'
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g64p_P, g64g_ali,
    Matrix.of_apply, initialCodeState, emptyResource, forwardResource, taskTarget, g64g_kr, hk]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one]
  obtain ⟨u0, x, u1, u2⟩ := i
  obtain ⟨v0, y, v1, v2⟩ := j
  obtain rfl : u0 = default := Subsingleton.elim _ _
  obtain rfl : v0 = default := Subsingleton.elim _ _
  obtain rfl : u1 = default := Subsingleton.elim _ _
  obtain rfl : v1 = default := Subsingleton.elim _ _
  obtain rfl : u2 = default := Subsingleton.elim _ _
  obtain rfl : v2 = default := Subsingleton.elim _ _
  rw [g64g_x1 x, g64g_x1 y]
  generalize x 0 = a0, y 0 = b0
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, g64g_kr, g64g_s1, g64g_s2, Fin.sum_univ_four,
    pow_one, pow_zero, Real.sqrt_one, Complex.ofReal_one, inv_one]
  have hc : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = g64g_c := rfl
  simp only [hc]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  cases a0 <;> cases b0 <;>
    simp [g64p_B, g64p_E, g64g_pz, g64g_g, g64g_veq, g64g_feq, g64g_cc, e1]
  all_goals
    have hc4 : g64g_c ^ 4 = 1 / 4 := by
      rw [show g64g_c ^ 4 = (g64g_c * g64g_c) * (g64g_c * g64g_c) by ring, g64g_c2]; norm_num
    ring_nf
    try rw [hc4]
    try ring
  all_goals (congr 2 <;> exact Subsingleton.elim _ _)

theorem solution :
    ExactConversion emptyResource 1 0 2 (taskTarget 1 0 0) := g64p_main

end
