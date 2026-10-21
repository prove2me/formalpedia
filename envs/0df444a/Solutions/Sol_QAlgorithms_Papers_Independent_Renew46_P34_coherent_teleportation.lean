-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.coherent_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:47:59.884281+00:00
-- url     : https://prove2.me/submissions/2b6c2f6b-eb52-46a4-b80a-5499e64b0b7a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P34
instance g65g_uq : Unique (Qubits 0) := Pi.uniqueOfIsEmpty _

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


def g65g_enc : Superop ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) (Qubits 2 × (Fin 1 × (Qubits 0 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ∑ s : Qubits 1, ∑ a : Qubits 1, ∑ s' : Qubits 1, ∑ a' : Qubits 1,
    g65g_pz o.1 (s 0) (a 0) * g65g_c * ρ ((s, default), ((), a)) ((s', default), ((), a')) *
      (g65g_pz o'.1 (s' 0) (a' 0) * g65g_c)

def g65g_ali : Superop (Qubits 2 × Fin 1) (Qubits 2) :=
  fun ρ => Matrix.of fun o o' => ρ (o, 0) (o', 0)

def g65g_bob : Superop (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) (Qubits 1 × (Qubits 0 × Qubits 2)) :=
  fun ρ => Matrix.of fun o o' => ∑ b : Qubits 1, ∑ b' : Qubits 1,
    g65g_pz o.2.2 (o.1 0) (b 0) * ρ (o.2.2, ((), (b, (default, default)))) (o'.2.2, ((), (b', (default, default)))) *
      g65g_pz o'.2.2 (o'.1 0) (b' 0)

lemma g65g_perm (x : Qubits 2) (r s : Qubits 1) :
    ∑ b : Qubits 1, g65g_pz x (r 0) (b 0) * g65g_pz x (s 0) (b 0) = if r = s then 1 else 0 := by
  rw [g65g_x2 x, g65g_x1 r, g65g_x1 s]
  generalize x 0 = a, x 1 = b, r 0 = c, s 0 = d
  simp only [g65g_s1, g65g_feq]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [g65g_pz]

lemma g65g_reorder (F : Qubits 1 → Qubits 1 → Qubits 1 → Qubits 1 → ℂ) :
    ∑ x, ∑ x1, ∑ x2, ∑ x3, F x x1 x2 x3 = ∑ x2, ∑ x3, ∑ x, ∑ x1, F x x1 x2 x3 := by
  calc _ = ∑ x, ∑ x2, ∑ x1, ∑ x3, F x x1 x2 x3 := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ x2, ∑ x3, ∑ x1, F x x1 x2 x3 :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x2, ∑ x, ∑ x3, ∑ x1, F x x1 x2 x3 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

def g65g_V : Fin 1 → Matrix (Qubits 2 × (Fin 1 × (Qubits 0 × Qubits 0))) ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ℂ :=
  fun _ o i => g65g_pz o.1 (i.1.1 0) (i.2.2 0) * g65g_c

def g65g_A : Fin 1 → Matrix (Qubits 2) (Qubits 2 × Fin 1) ℂ :=
  fun _ o i => if i.1 = o then 1 else 0

def g65g_B : Fin 1 → Matrix (Qubits 1 × (Qubits 0 × Qubits 2)) (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) ℂ :=
  fun _ o i => if o.2.2 = i.1 then g65g_pz i.1 (o.1 0) (i.2.2.1 0) else 0

lemma g65g_V_kraus : IsKrausFamily g65g_V := by
  unfold IsKrausFamily
  ext ⟨⟨s, u⟩, w, a⟩ ⟨⟨s', u'⟩, w', a'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  rw [g65g_x1 s, g65g_x1 s', g65g_x1 a, g65g_x1 a']
  generalize s 0 = a0, s' 0 = b0, a 0 = c0, a' 0 = d0
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s2, Fin.sum_univ_one, Matrix.one_apply]
  have hc2 := g65g_c2
  cases a0 <;> cases b0 <;> cases c0 <;> cases d0 <;>
    simp [g65g_V, g65g_pz, g65g_feq, g65g_cc] <;> (ring_nf; try rw [show g65g_c ^ 2 = 1 / 2 by rw [sq, g65g_c2]]; try norm_num)

lemma g65g_enc_eq (ρ : Matrix ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ((Qubits 1 × Qubits 0) × (Unit × Qubits 1)) ℂ) :
    g65g_enc ρ = krausApply g65g_V ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_enc, g65g_V, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    map_mul, g65g_pzc, g65g_cc]
  congr!

lemma g65g_A_kraus : IsKrausFamily g65g_A := by
  unfold IsKrausFamily
  ext ⟨x, m⟩ ⟨x', m'⟩
  obtain rfl : m = m' := Subsingleton.elim _ _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one, Matrix.one_apply]
  simp [g65g_A, Prod.ext_iff]

lemma g65g_ali_eq (ρ : Matrix (Qubits 2 × Fin 1) (Qubits 2 × Fin 1) ℂ) : g65g_ali ρ = krausApply g65g_A ρ := by
  ext o o'
  rw [g65g_kr]
  simp [g65g_ali, g65g_A, Fintype.sum_prod_type, Finset.sum_ite_eq']

lemma g65g_B_kraus : IsKrausFamily g65g_B := by
  unfold IsKrausFamily
  ext ⟨y, w, b, u⟩ ⟨y', w', b', u'⟩
  obtain rfl : u = u' := Subsingleton.elim _ _
  rw [g65g_x2 y, g65g_x2 y', g65g_x1 b, g65g_x1 b']
  generalize y 0 = a0, y 1 = a1, y' 0 = b0, y' 1 = b1, b 0 = c0, b' 0 = d0
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, g65g_s1, g65g_s2, Fin.sum_univ_one, Matrix.one_apply]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c0 <;> cases d0 <;>
    simp [g65g_B, g65g_pz, g65g_veq, g65g_feq] <;> norm_num

lemma g65g_bob_eq (ρ : Matrix (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0))))
    (Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) ℂ) :
    g65g_bob ρ = krausApply g65g_B ρ := by
  ext o o'
  rw [g65g_kr]
  simp only [g65g_bob, g65g_B, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_one,
    apply_ite (starRingEnd ℂ), map_zero, g65g_pzc, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ (y : Qubits 2) (b : Qubits 1),
      ((y, (), b, (@default (Qubits 0) Pi.instInhabited), (@default (Qubits 0) Pi.instInhabited)) :
        Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) = (y, default, b, default, default) :=
    fun y b => Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))))
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have k1 : ∀ (y : Qubits 2) (b : Qubits 1),
      ((y, (), b, (@default (Qubits 0) Pi.instInhabited), (@default (Qubits 0) Pi.instInhabited)) :
        Qubits 2 × (Unit × (Qubits 1 × (Qubits 0 × Qubits 0)))) =
      (y, (@default Unit _), b, (@default (Qubits 0) Unique.instInhabited), (@default (Qubits 0) Unique.instInhabited)) :=
    fun y b => Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))))
  rw [k1, k1]

abbrev g65g_P : OneWayCode Unit Unit (Qubits 2) (Qubits 2) (Qubits 2) (TaskInput 1 0) (Qubits 2) (TaskBob 1 0 2) where
  e := 1
  q := 0
  c := 0
  memory := 1
  memoryPositive := by norm_num
  encoder := g65g_enc
  aliceDecoder := g65g_ali
  bobDecoder := g65g_bob
  encoderChannel := ⟨1, g65g_V, by convert g65g_V_kraus, fun ρ => by convert g65g_enc_eq ρ⟩
  aliceChannel := ⟨1, g65g_A, by convert g65g_A_kraus, fun ρ => by convert g65g_ali_eq ρ⟩
  bobChannel := ⟨1, g65g_B, by convert g65g_B_kraus, fun ρ => by convert g65g_bob_eq ρ⟩

theorem g65g_main :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) := by
  refine ⟨g65g_P, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g65g_P, g65g_enc, g65g_ali, g65g_bob,
    Matrix.of_apply, initialCodeState, coherentResource, taskTarget]
  simp only [Matrix.of_apply, emptySource, pureDensity, maxEntangled, mul_one]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  simp only [e1, if_true]
  obtain ⟨oA, r, u, oB⟩ := i
  obtain ⟨oA', r', u', oB'⟩ := j
  obtain rfl : u = default := Subsingleton.elim _ _
  obtain rfl : u' = default := Subsingleton.elim _ _
  simp only
  have hc1 : ((Real.sqrt (2 ^ 1) : ℝ) : ℂ)⁻¹ = g65g_c := by simp [g65g_c]
  have hc2 : ((Real.sqrt (2 ^ 2) : ℝ) : ℂ)⁻¹ = g65g_c * g65g_c := by
    rw [g65g_c2, show ((2:ℝ) ^ 2) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]; norm_num
  by_cases h : oA = oB ∧ oA' = oB'
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, hc1, hc2, apply_ite (starRingEnd ℂ), g65g_cc, map_zero, map_mul,
      mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ]
    calc _ = ∑ x2 : Qubits 1, ∑ x3 : Qubits 1,
          (∑ x1 : Qubits 1, g65g_pz oA' (x3 0) (x1 0) * g65g_pz oA' (r' 0) (x1 0)) *
          (∑ x : Qubits 1, g65g_pz oA (r 0) (x 0) * g65g_pz oA (x2 0) (x 0)) *
          (M (x2, default) (x3, default) * (g65g_c * g65g_c * (g65g_c * g65g_c))) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine (g65g_reorder _).trans ?_
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
            ring
      _ = _ := by
            simp only [g65g_perm, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
              Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have : (if oA = oB then g65g_c * g65g_c else 0) * (if oA' = oB' then g65g_c * g65g_c else 0) = 0 := by
      rcases not_and_or.1 h with h | h <;> simp [h]
    simp only [h, if_false, mul_zero, zero_mul, Finset.sum_const_zero, hc2, apply_ite (starRingEnd ℂ),
      map_zero, map_mul, g65g_cc]
    rw [this, mul_zero]

theorem solution :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) := g65g_main
