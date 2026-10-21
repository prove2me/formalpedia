-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.coherent_superdense_coding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:28:55.909981+00:00
-- url     : https://prove2.me/submissions/45747be6-4fd0-41f5-838e-6cef1a32ad9e

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P34
lemma g65g_kr {K ι κ : Type} [Fintype K] [Fintype ι] (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) (i j : κ) :
    krausApply E ρ i j = ∑ k, ∑ a, ∑ b, E k i a * ρ a b * conj (E k j b) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]; rfl

lemma g65g_s1 (f : Qubits 1 → ℂ) : ∑ b, f b = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]; rfl

lemma g65g_s2 (f : Qubits 2 → ℂ) : ∑ b, f b = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  simp [finTwoArrowEquiv]; ring

def g65g_pz (x : Qubits 2) (q a : Bool) : ℂ := if q = xor a (x 0) then (if (x 1 && a) then -1 else 1) else 0

def g65g_g (k : Fin 4) : Qubits 2 := ![decide (k.val % 2 = 1), decide (k.val / 2 = 1)]

def g65g_c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma g65g_feq (a b : Bool) : ((fun _ : Fin 1 => a) = (fun _ => b)) = (a = b) := by
  apply propext; constructor
  · intro h; exact congrFun h 0
  · intro h; rw [h]

lemma g65g_c2 : g65g_c * g65g_c = 1 / 2 := by
  unfold g65g_c
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma g65g_veq (a b c d : Bool) : (![a, b] = ![c, d]) = (a = c ∧ b = d) := by
  apply propext; constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma g65g_pzc (x : Qubits 2) (q a : Bool) : (starRingEnd ℂ) (g65g_pz x q a) = g65g_pz x q a := by
  unfold g65g_pz; split_ifs <;> simp

lemma g65g_cc : (starRingEnd ℂ) g65g_c = g65g_c := by
  unfold g65g_c; rw [map_inv₀, Complex.conj_ofReal]

lemma g65g_x2 (x : Qubits 2) : x = ![x 0, x 1] := by funext t; fin_cases t <;> rfl
lemma g65g_x1 (x : Qubits 1) : x = fun _ => x 0 := by funext t; fin_cases t; rfl


def g65g_idx (x : Qubits 2) : Fin 4 := ⟨(x 0).toNat + 2 * (x 1).toNat, by
  cases x 0 <;> cases x 1 <;> simp⟩

lemma g65g_gidx (x : Qubits 2) : g65g_g (g65g_idx x) = x := by
  rw [g65g_x2 x]; generalize x 0 = a, x 1 = b
  cases a <;> cases b <;> rfl

lemma g65g_idxg (m : Fin 4) : g65g_idx (g65g_g m) = m := by
  fin_cases m <;> rfl

def g65g_enc : Superop (Qubits 2 × (Unit × Qubits 1)) (Unit × (Fin 4 × (Qubits 1 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ∑ a : Qubits 1, ∑ a' : Qubits 1,
    g65g_pz (g65g_g o.2.1) (o.2.2.1 0) (a 0) * ρ (g65g_g o.2.1, ((), a)) (g65g_g o'.2.1, ((), a')) *
      g65g_pz (g65g_g o'.2.1) (o'.2.2.1 0) (a' 0)

def g65g_ali : Superop (Unit × Fin 4) (Qubits 2) :=
  fun ρ => Matrix.of fun o o' => ρ ((), g65g_idx o) ((), g65g_idx o')

def g65g_bob : Superop (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) (Qubits 2) :=
  fun ρ => Matrix.of fun o o' => ∑ e : Qubits 1, ∑ q : Qubits 1, ∑ e' : Qubits 1, ∑ q' : Qubits 1,
    g65g_pz o (q 0) (e 0) * g65g_c * ρ ((), ((), (e, (q, default)))) ((), ((), (e', (q', default)))) *
      (g65g_pz o' (q' 0) (e' 0) * g65g_c)

lemma g65g_beta (x y : Qubits 2) :
    ∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz y (q 0) (e 0) * g65g_pz x (q 0) (e 0) =
      if x = y then 2 else 0 := by
  rw [g65g_x2 x, g65g_x2 y]
  generalize x 0 = a, x 1 = b, y 0 = c, y 1 = d
  simp only [g65g_s1, g65g_veq]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [g65g_pz] <;> norm_num


def g65g_V : Fin 1 → Matrix (Unit × (Fin 4 × (Qubits 1 × Qubits 0))) (Qubits 2 × (Unit × Qubits 1)) ℂ :=
  fun _ o i => if i.1 = g65g_g o.2.1 then g65g_pz (g65g_g o.2.1) (o.2.2.1 0) (i.2.2 0) else 0

def g65g_A : Fin 1 → Matrix (Qubits 2) (Unit × Fin 4) ℂ :=
  fun _ o i => if i.2 = g65g_idx o then 1 else 0

def g65g_B : Fin 1 → Matrix (Qubits 2) (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) ℂ :=
  fun _ o i => g65g_pz o (i.2.2.2.1 0) (i.2.2.1 0) * g65g_c

lemma g65g_V_kraus : IsKrausFamily g65g_V := by
  unfold IsKrausFamily
  ext ⟨x, u, a⟩ ⟨x', u', a'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  rw [g65g_x2 x, g65g_x2 x', g65g_x1 a, g65g_x1 a']
  generalize x 0 = a0, x 1 = a1, x' 0 = b0, x' 1 = b1, a 0 = c0, a' 0 = d0
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s1, Fin.sum_univ_four, Matrix.one_apply]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases d0 <;>
    simp [g65g_V, g65g_pz, g65g_g, g65g_veq, g65g_feq] <;> norm_num

lemma g65g_enc_eq (ρ : Matrix (Qubits 2 × (Unit × Qubits 1)) (Qubits 2 × (Unit × Qubits 1)) ℂ) :
    g65g_enc ρ = krausApply g65g_V ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_enc, g65g_V, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique]
  simp [Finset.sum_ite_eq', g65g_pzc, apply_ite (starRingEnd ℂ)]

lemma g65g_A_kraus : IsKrausFamily g65g_A := by
  unfold IsKrausFamily
  ext ⟨u, m⟩ ⟨u', m'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_unique, g65g_s2, Matrix.one_apply]
  fin_cases m <;> fin_cases m' <;> simp [g65g_A, g65g_idx] <;> decide

lemma g65g_ali_eq (ρ : Matrix (Unit × Fin 4) (Unit × Fin 4) ℂ) : g65g_ali ρ = krausApply g65g_A ρ := by
  ext o o'
  rw [g65g_kr]
  simp [g65g_ali, g65g_A, Fintype.sum_prod_type, Finset.sum_ite_eq']

lemma g65g_B_kraus : IsKrausFamily g65g_B := by
  unfold IsKrausFamily
  ext ⟨u, w, e, q, c⟩ ⟨u', w', e', q', c'⟩
  rw [g65g_x1 e, g65g_x1 e', g65g_x1 q, g65g_x1 q']
  generalize e 0 = a0, e' 0 = b0, q 0 = c0, q' 0 = d0
  obtain rfl : c = c' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s2, Fin.sum_univ_one, Matrix.one_apply]
  have hc2 := g65g_c2
  cases a0 <;> cases b0 <;> cases c0 <;> cases d0 <;>
    simp [g65g_B, g65g_pz, g65g_feq, g65g_cc] <;> (ring_nf; try rw [show g65g_c ^ 2 = 1 / 2 by rw [sq, g65g_c2]]; try norm_num)

lemma g65g_bob_eq (ρ : Matrix (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) (Unit × (Unit × (Qubits 1 × (Qubits 1 × Qubits 0)))) ℂ) :
    g65g_bob ρ = krausApply g65g_B ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_bob, g65g_B, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    map_mul, g65g_pzc, g65g_cc]
  congr!

abbrev g65g_P : OneWayCode Unit Unit Unit Unit Unit (Qubits 2) (Qubits 2) (Qubits 2) where
  e := 1
  q := 1
  c := 0
  memory := 4
  memoryPositive := by norm_num
  encoder := g65g_enc
  aliceDecoder := g65g_ali
  bobDecoder := g65g_bob
  encoderChannel := ⟨1, g65g_V, by convert g65g_V_kraus, fun ρ => by convert g65g_enc_eq ρ⟩
  aliceChannel := ⟨1, g65g_A, by convert g65g_A_kraus, fun ρ => by convert g65g_ali_eq ρ⟩
  bobChannel := ⟨1, g65g_B, by convert g65g_B_kraus, fun ρ => by convert g65g_bob_eq ρ⟩

theorem g65g_main :
    ExactConversion emptyResource 1 1 0 (coherentResource 2) := by
  refine ⟨g65g_P, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g65g_P, g65g_enc, g65g_ali, g65g_bob,
    Matrix.of_apply, initialCodeState, emptyResource, forwardResource, coherentResource]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one, g65g_gidx]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  simp only [e1, if_true]
  obtain ⟨oA, oB⟩ := i
  obtain ⟨oA', oB'⟩ := j
  simp only
  have hc : ((Real.sqrt (2 ^ 1) : ℝ) : ℂ)⁻¹ = g65g_c := by simp [g65g_c]
  simp only [hc, apply_ite (starRingEnd ℂ), map_zero, g65g_cc, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ x y : Qubits 2, ∑ e : Qubits 1, ∑ q : Qubits 1,
      g65g_pz y (q 0) (e 0) * g65g_pz x (q 0) (e 0) = if x = y then 2 else 0 := g65g_beta
  calc _ = (∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz oB' (q 0) (e 0) * g65g_pz oA' (q 0) (e 0)) *
        (∑ e : Qubits 1, ∑ q : Qubits 1, g65g_pz oB (q 0) (e 0) * g65g_pz oA (q 0) (e 0)) *
        (M oA oA' * (g65g_c * g65g_c) * (g65g_c * g65g_c)) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          ring
    _ = _ := by
          rw [key, key, g65g_c2]
          by_cases h1 : oA = oB <;> by_cases h2 : oA' = oB' <;> simp [h1, h2] <;> ring

theorem solution :
    ExactConversion emptyResource 1 1 0 (coherentResource 2) := g65g_main
